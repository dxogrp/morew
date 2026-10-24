/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Affine
import Morew.Core
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.RecExt

/-!
# Bounded helper expansion for affine certification

Expansion supplies a temporary, definitionally equal expression to the affine
certifier. It never changes stored model expressions. Arithmetic operation
prefixes, proof terms, local evidence, and unsupported native operations remain
intact; only ordinary transparent, nonrecursive helper definitions are opened.
-/

/-- Maximum nested helper expansions; zero disables expansion. -/
register_option morew.affine.maxExpansionDepth : Nat := {
  defValue := 32
  descr := "Maximum nested helper expansions during affine certification (zero disables expansion)"
}

/-- Maximum helper unfoldings shared across branches; zero disables expansion. -/
register_option morew.affine.maxExpansionSteps : Nat := {
  defValue := 1024
  descr := "Maximum helper unfoldings during affine certification (zero disables expansion)"
}

/-- Maximum cumulative expanded expression size; zero disables expansion. -/
register_option morew.affine.maxExpansionNodes : Nat := {
  defValue := 100000
  descr := "Maximum cumulative expanded expression size during affine certification (zero disables expansion)"
}

namespace Morew.Elab.Affine.Expansion

open Lean Lean.Meta

/-- The temporary expression and the number of helper occurrences expanded. -/
structure Result where
  /-- A definitionally equal expression used only for proof construction. -/
  expression : Expr
  /-- Number of helper occurrences expanded, counting repeated applications. -/
  expansions : Nat

private structure Limits where
  depth : Nat
  steps : Nat
  nodes : Nat

private def limits : MetaM Limits := do
  let options ← getOptions
  return {
    depth := morew.affine.maxExpansionDepth.get options
    steps := morew.affine.maxExpansionSteps.get options
    nodes := morew.affine.maxExpansionNodes.get options
  }

/-- Whether every helper-expansion budget is nonzero. -/
def enabled : MetaM Bool := do
  let bounds ← limits
  return bounds.depth != 0 && bounds.steps != 0 && bounds.nodes != 0

private structure State where
  steps : Nat := 0
  nodes : Nat := 0
  cache : ExprMap Expr := {}
  helper? : Option Expr := none

private abbrev ExpandM := StateRefT State MetaM

-- Saturating arithmetic makes preflight costs independent of large argument
-- duplication. Counting stops as soon as the available budget is exceeded.
private def cappedAdd (cap a b : Nat) : Nat := min (cap + 1) (a + b)

private partial def expressionSize (expression : Expr) (cap : Nat)
    (arguments : Array Nat := #[]) (offset : Nat := 0) : Nat :=
  if cap == 0 then 1 else
  match expression with
  | .bvar index =>
    if offset ≤ index && index - offset < arguments.size then
      min (cap + 1) arguments[arguments.size - 1 - (index - offset)]!
    else 1
  | .app f a =>
    let first := expressionSize f (cap - 1) arguments offset
    if first ≥ cap then cap + 1
    else 1 + first + expressionSize a (cap - 1 - first) arguments offset
  | .lam _ type body _ | .forallE _ type body _ =>
    let first := expressionSize type (cap - 1) arguments offset
    if first ≥ cap then cap + 1
    else 1 + first + expressionSize body (cap - 1 - first) arguments (offset + 1)
  | .letE _ type value body _ =>
    let first := expressionSize type (cap - 1) arguments offset
    if first ≥ cap then cap + 1 else
    let second := expressionSize value (cap - 1 - first) arguments offset
    if first + second ≥ cap then cap + 1
    else 1 + first + second +
      expressionSize body (cap - 1 - first - second) arguments (offset + 1)
  | .proj _ _ value | .mdata _ value =>
    1 + expressionSize value (cap - 1) arguments offset
  | _ => 1

-- Estimate the complete beta result before instantiating any arguments. Each
-- occurrence of a parameter pays for its argument, even if the DAG shares it.
private def applicationSize (value : Expr) (arguments : Array Expr) (cap : Nat) : Nat := Id.run do
  if arguments.isEmpty then return expressionSize value cap
  let mut body := value.consumeMData
  let mut used := 0
  while used < arguments.size do
    match body with
    | .lam _ _ next _ =>
      used := used + 1
      body := next.consumeMData
    | _ => break
  let sizes := (arguments.extract 0 used).map (expressionSize · cap)
  let mut size := expressionSize body cap sizes
  for argument in arguments[used:] do
    if size > cap then return cap + 1
    size := cappedAdd cap (size + 1) (expressionSize argument cap)
  return size

-- The exact prefix is retained for the certifier's canonical instance checks.
-- This is deliberately not a generic traversal of application arguments.
private def operandStart? (name : Name) (arity : Nat) : Option Nat :=
  if ([``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HSMul.hSMul,
      ``HPow.hPow].contains name) && arity == 6 then some 4
  else if name == ``Neg.neg && arity == 3 then some 2
  else if ([``Prod.mk, ``Matrix.vecCons].contains name) && arity == 4 then some 2
  else if name == ``Finset.sum && arity == 5 then some 3
  else if ([`Finset.sup', `Finset.inf'].contains name) && arity == 6 then some 3
  else if ([``dotProduct, ``Matrix.mulVec, ``Matrix.vecMul].contains name) && arity == 7 then some 5
  else if ([``WithLp.toLp, ``WithLp.ofLp].contains name) && arity == 3 then some 2
  else if ([``LE.le, ``GE.ge, ``LT.lt].contains name) && arity == 4 then some 2
  else if name == ``Eq && arity == 3 then some 1
  else if name == ``And && arity == 2 then some 0
  else if name == ``Membership.mem && arity == 5 then some 3
  else if ([`Real.exp, `Real.log, `Real.sqrt, `Real.sin, `Real.cos, `Real.tan,
      `Real.arcsin, `Real.arccos, `Real.arctan, `Real.sinh, `Real.cosh,
      `Real.tanh, `Complex.exp, `Complex.log].contains name) && arity == 1 then some 0
  else if name == `Real.rpow && arity == 2 then some 0
  else if ([``Norm.norm, ``NNNorm.nnnorm, ``ENorm.enorm, `Inv.inv, `PosPart.posPart].contains name) &&
      arity == 3 then some 2
  else if name == `abs && arity == 4 then some 3
  else if ([`Min.min, `Max.max].contains name) && arity == 4 then some 2
  else none

private def nativeBoundary (name : Name) : Bool :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HSMul.hSMul,
    ``HPow.hPow, ``Neg.neg, ``Prod.mk, ``Matrix.vecCons, ``Matrix.vecEmpty, ``Fin.elim0,
    ``Finset.sum, `Finset.sup', `Finset.inf',
    ``dotProduct, ``Matrix.mulVec, ``Matrix.vecMul, ``WithLp.toLp, ``WithLp.ofLp,
    ``LE.le, ``GE.ge, ``LT.lt, ``Eq, ``And, ``Membership.mem,
    `ite, `dite, `cond, `Decidable.decide, `abs, ``Norm.norm, ``NNNorm.nnnorm, ``ENorm.enorm,
    `Inv.inv, `Min.min, `Max.max, `PosPart.posPart, `min, `max, `Finset.prod, `tsum,
    `Real.exp, `Real.log, `Real.sqrt, `Real.rpow, `Real.sin, `Real.cos,
    `Real.tan, `Real.arcsin, `Real.arccos, `Real.arctan, `Real.sinh,
    `Real.cosh, `Real.tanh, `Complex.exp, `Complex.log].contains name

private structure Helper where
  value : Expr
  levelParams : List Name
  levels : List Level

private def helperValue? (expression : Expr) : MetaM (Option Helper) := do
  let .const name levels := expression.getAppFn | return none
  if nativeBoundary name then return none
  let environment ← getEnv
  if environment.isProjectionFn name then return none
  if (← getMatcherInfo? name).isSome then return none
  if ← isRecursiveDefinition name then return none
  if (← getReducibilityStatus name) == .irreducible then return none
  -- Transcendental primitive implementations are recognition boundaries, even
  -- when implemented by transparent definitions rather than opaque constants.
  if let some index := environment.getModuleIdxFor? name then
    let moduleName := environment.header.modules[index.toNat]!.module
    if (`Mathlib.Analysis.SpecialFunctions).isPrefixOf moduleName then return none
  let .defnInfo declaration ← getConstInfo name | return none
  unless declaration.safety == .safe do return none
  -- Do not discover a hidden constraint by unfolding a predicate or a proof.
  let type ← inferType expression
  if ← isProp type then return none
  let returnsType ← forallTelescopeReducing type fun _ result => do
    return (← whnf result).isSort
  if returnsType then return none
  return some { value := declaration.value, levelParams := declaration.levelParams, levels }

private def exhausted (source : Expr) (option : Name) (limit : Nat) : ExpandM α :=
  throwError "affine helper expansion of {source} exhausted {option} (limit {limit})"

private def chargeBeta (value : Expr) (arguments : Array Expr) (bounds : Limits) :
    ExpandM Unit := do
  let state ← get
  let cost := applicationSize value arguments (bounds.nodes - state.nodes)
  if cost > bounds.nodes - state.nodes then
    exhausted (state.helper?.getD value) `morew.affine.maxExpansionNodes bounds.nodes
  modify fun state => { state with nodes := state.nodes + cost }

-- A helper can expose a higher-order beta redex, for example
-- `apply (fun x => x + x) largeArgument`. Check that substitution as well as
-- the initial delta-beta step; otherwise its duplicated arguments evade the
-- node budget. Original helper-free structural reduction stays unchanged.
private partial def reduceChecked (source : Expr) (reduce : Expr → Bool → MetaM Expr)
    (bounds : Limits) : ExpandM Expr := do
  if (← get).steps == 0 then return ← reduce source true
  let expression := (← instantiateMVars source).consumeMData
  match expression with
  | .fvar id =>
    if let some value := (← id.getDecl).value? (allowNondep := true) then
      -- Repeated local aliases duplicate their bodies in the temporary tree,
      -- even though the original let expression stored that body only once.
      chargeBeta value #[] bounds
      return ← reduceChecked value reduce bounds
    return expression
  | .letE .. => return expression
  | .proj name index value =>
    let value ← reduceChecked value reduce bounds
    if name == ``Prod && value.isAppOf ``Prod.mk then
      return ← reduceChecked value.getAppArgs[index + 2]! reduce bounds
    return .proj name index value
  | .app .. =>
    let arguments := expression.getAppArgs
    let function ← reduceChecked expression.getAppFn reduce bounds
    if let .letE name type value body nondep := function then
      return .letE name type value
        (mkAppN body (arguments.map (·.liftLooseBVars 0 1))) nondep
    if function.isLambda then
      chargeBeta function arguments bounds
      return ← reduceChecked (function.beta arguments) reduce bounds
    if (function.isConstOf ``Prod.casesOn || function.isConstOf ``Prod.rec) &&
        arguments.size ≥ 5 then
      let value := arguments[if function.isConstOf ``Prod.casesOn then 3 else 4]!
      let branch := arguments[if function.isConstOf ``Prod.casesOn then 4 else 3]!
      let fields := #[Expr.proj ``Prod 0 value, Expr.proj ``Prod 1 value]
      chargeBeta branch fields bounds
      return ← reduceChecked (mkAppN (branch.beta fields)
        (arguments.extract 5 arguments.size)) reduce bounds
    if let some name := function.constName? then
      if let some matcher ← getMatcherInfo? name then
        if matcher.numAlts == 1 && arguments.size ≥ matcher.arity then
          let mut productsOnly := decide (matcher.numDiscrs > 0)
          for i in [matcher.getFirstDiscrPos:matcher.getFirstAltPos] do
            let type ← whnf (← inferType arguments[i]!)
            productsOnly := productsOnly && type.isAppOfArity ``Prod 2
          if productsOnly then
            let declaration ← getConstInfo name
            if let some value := declaration.value? then
              chargeBeta value arguments bounds
              let value := value.instantiateLevelParams
                declaration.levelParams function.constLevels!
              return ← reduceChecked (value.beta arguments) reduce bounds
    if (function.isConstOf ``Prod.fst || function.isConstOf ``Prod.snd) &&
        arguments.size ≥ 3 then
      let projection := Expr.proj ``Prod
        (if function.isConstOf ``Prod.fst then 0 else 1) arguments[2]!
      return ← reduceChecked (mkAppN projection (arguments.extract 3 arguments.size))
        reduce bounds
    if (function.isConstOf ``Morew.Problem.objective ||
        function.isConstOf ``Morew.Problem.feasible) && arguments.size ≥ 3 then
      -- Match the existing container-field reduction even after earlier
      -- branches have expanded helpers. Visit the selected function so its
      -- beta reductions and helper applications still consume this budget.
      let problem ← whnf arguments[2]!
      if problem.isAppOf ``Morew.Problem.mk then
        let index := if function.isConstOf ``Morew.Problem.objective then 2 else 3
        return ← reduceChecked (mkAppN problem.getAppArgs[index]!
          (arguments.extract 3 arguments.size)) reduce bounds
    return mkAppN function arguments
  | _ => return expression

private partial def visit (source : Expr) (reduce : Expr → Bool → MetaM Expr)
    (bounds : Limits) (depth : Nat) : ExpandM Expr := do
  let expression ← reduceChecked source reduce bounds
  match expression with
  | .lam name type body info =>
    return ← withLocalDecl name info type fun binding => do
      let body ← visit (body.instantiate1 binding) reduce bounds depth
      return .lam name type (body.abstract #[binding]) info
  | .forallE name type body info =>
    return ← withLocalDecl name info type fun binding => do
      let body ← visit (body.instantiate1 binding) reduce bounds depth
      return .forallE name type (body.abstract #[binding]) info
  | .letE name type value body nondep =>
    -- Evidence and instances must stay in scope, including unused proof lets.
    let value ← if (← isProp type) || (← isClass? type).isSome then pure value
      else visit value reduce bounds depth
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let body ← visit (body.instantiate1 binding) reduce bounds depth
      return .letE name type value (body.abstract #[binding]) nondep
  | .proj name index value =>
    return .proj name index (← visit value reduce bounds depth)
  | _ => pure ()
  let head := expression.getAppFn
  let arguments := expression.getAppArgs
  if let some name := head.constName? then
    if let some first := operandStart? name arguments.size then
      let mut expanded := arguments
      for i in [first:arguments.size] do
        expanded := expanded.set! i (← visit arguments[i]! reduce bounds depth)
      return mkAppN head expanded
  if let some helper ← helperValue? expression then
    if depth ≥ bounds.depth then
      exhausted expression `morew.affine.maxExpansionDepth bounds.depth
    let state ← get
    if state.steps ≥ bounds.steps then
      exhausted expression `morew.affine.maxExpansionSteps bounds.steps
    let cost := applicationSize helper.value arguments (bounds.nodes - state.nodes)
    if cost > bounds.nodes - state.nodes then
      exhausted expression `morew.affine.maxExpansionNodes bounds.nodes
    let expanded := match state.cache[expression]? with
      | some expanded => expanded
      | none =>
        let value := helper.value.instantiateLevelParams helper.levelParams helper.levels
        value.beta arguments
    modify fun state => { state with
      steps := state.steps + 1
      nodes := state.nodes + cost
      cache := state.cache.insert expression expanded
      helper? := some expression }
    return ← visit expanded reduce bounds (depth + 1)
  -- An applied local vector or lambda may contain helper expressions. Unknown
  -- constant heads remain boundaries, including predicates and native atoms.
  if !head.isConst then
    if let .app function argument := expression then
      return mkApp (← visit function reduce bounds depth)
        (← visit argument reduce bounds depth)
  return expression

/-- Prepare one source expression with one shared budget. The supplied reducer
handles only existing structural reductions; helper unfolding lives here.
Proof and instance lets remain available to evidence collection and reification.
Zero in any option disables all helper expansion. -/
def prepare (source : Expr) (reduce : Expr → Bool → MetaM Expr) : MetaM Result := do
  let bounds ← limits
  if bounds.depth == 0 || bounds.steps == 0 || bounds.nodes == 0 then
    return { expression := source, expansions := 0 }
  let (expression, state) ← (visit source reduce bounds 0).run {}
  return { expression, expansions := state.steps }

/-- Expand safe helper heads without modifying the source presentation. -/
def expand (source : Expr) (reduce : Expr → Bool → MetaM Expr) : MetaM Expr := do
  return (← prepare source reduce).expression

end Morew.Elab.Affine.Expansion
