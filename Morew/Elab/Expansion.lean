/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Block
import Morew.Core
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.RecExt

/-!
# Bounded expansion of transparent value helpers

Certifiers share one-head unfolding, resource accounting, and checked
structural reduction. Each consumer chooses when to unfold and which operands
to visit; this module never traverses a source expression eagerly.
-/

namespace Morew.Elab.Expansion

open Lean Lean.Meta

/-- Resource bounds and the option names used in exhaustion diagnostics. -/
structure Config where
  /-- Maximum number of nested helper unfoldings. -/
  depth : Nat
  /-- Maximum helper occurrences unfolded in one session. -/
  steps : Nat
  /-- Maximum cumulative size charged before substitutions. -/
  nodes : Nat
  /-- Locally scoped option controlling the depth limit. -/
  depthOption : Name
  /-- Locally scoped option controlling the occurrence limit. -/
  stepsOption : Name
  /-- Locally scoped option controlling the expression-size limit. -/
  nodesOption : Name
  /-- Certification family named in limit diagnostics. -/
  label : String

/-- Whether every helper-expansion budget is nonzero. -/
def enabled (config : Config) : Bool :=
  config.depth != 0 && config.steps != 0 && config.nodes != 0

/-- A limit failure before the over-budget expansion has been constructed. -/
structure LimitError where
  /-- Helper application responsible for the exhausted budget. -/
  expression : Expr
  /-- Option whose configured limit prevented further expansion. -/
  option : Name
  /-- Configured value of the exhausted option. -/
  limit : Nat
  /-- Preserve temporary binders after the expansion traversal unwinds. -/
  expressionMessage : MessageData := .ofExpr expression

/-- Format a limit error without losing the caller's certification family. -/
def LimitError.toMessageData (error : LimitError) (label : String) : MessageData :=
  m!"{label} helper expansion of {error.expressionMessage} exhausted {error.option} (limit {error.limit})"

/-- Shared accounting for one source expression. Cached occurrences still pay
for each expansion and its substituted expression size. -/
structure Session where
  /-- Number of helper occurrences already unfolded, including cache hits. -/
  steps : Nat := 0
  /-- Cumulative expression size already charged to this source. -/
  nodes : Nat := 0
  /-- Instantiated helper bodies; reuse does not waive occurrence or size costs. -/
  cache : ExprMap Expr := {}
  /-- Lexical helper responsible for the current structural substitution. -/
  helper? : Option Expr := none

/-- Expansion actions share accounting and return structured limit failures. -/
abbrev ExpandM := StateRefT Session (ExceptT LimitError MetaM)

/-- Run a shared expansion action, returning its accounting on success. -/
def run (action : ExpandM α) (state : Session := {}) :
    MetaM (Except LimitError (α × Session)) :=
  (action.run state).run

/-- One helper expansion, including its actual application for diagnostics. -/
structure Step where
  /-- Expression after opening one eligible helper head. -/
  expression : Expr
  /-- Original helper application, retained for lexical depth and diagnostics. -/
  helper : Expr

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

private def nativeBoundary (name : Name) : Bool :=
  [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HSMul.hSMul,
    ``HPow.hPow, ``Neg.neg, ``Prod.mk, ``Matrix.vecCons, ``Matrix.vecEmpty, ``Fin.elim0,
    ``Finset.sum, `Finset.sup', `Finset.inf',
    ``dotProduct, ``Matrix.mulVec, ``Matrix.vecMul, ``WithLp.toLp, ``WithLp.ofLp,
    ``Matrix.of, ``Matrix.transpose, ``Matrix.diagonal, ``Matrix.submatrix,
    ``Matrix.reindex, ``Matrix.fromBlocks,
    `Morew.Conic.fromBlocksFin, `Morew.Conic.SymmetricMatrix.toMatrix,
    `Morew.Conic.SymmetricMatrix.ofMatrix,
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

private def exhausted (source : Expr) (option : Name) (limit : Nat) : ExpandM α := do
  let expressionMessage ← addMessageContext m!"{source}"
  throwThe LimitError { expression := source, option, limit, expressionMessage }

/-- Charge a structural substitution exposed by an earlier helper unfolding.
The caller supplies its lexical helper in `Session.helper?` when traversing
multiple branches, so any exhaustion identifies the responsible application. -/
def chargeBeta (value : Expr) (arguments : Array Expr) (bounds : Config) :
    ExpandM Unit := do
  let state ← get
  let cost := applicationSize value arguments (bounds.nodes - state.nodes)
  if cost > bounds.nodes - state.nodes then
    exhausted (state.helper?.getD value) bounds.nodesOption bounds.nodes
  modify fun state => { state with nodes := state.nodes + cost }

-- Ordinary helpers and helpers exposing a problem container use the same
-- eligibility, cache, and pre-substitution accounting.
private def unfoldHelper (expression : Expr) (helper : Helper) (bounds : Config)
    (depth : Nat) : ExpandM Expr := do
  if depth ≥ bounds.depth then
    exhausted expression bounds.depthOption bounds.depth
  let state ← get
  if state.steps ≥ bounds.steps then
    exhausted expression bounds.stepsOption bounds.steps
  let arguments := expression.getAppArgs
  let cost := applicationSize helper.value arguments (bounds.nodes - state.nodes)
  if cost > bounds.nodes - state.nodes then
    exhausted expression bounds.nodesOption bounds.nodes
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
  return expanded

/-- Open one eligible ordinary value-helper head, with pre-substitution
accounting. This includes data-container definitions; consumers choose which
result shapes to admit. Arguments and resulting children are not visited. -/
def unfoldHead? (config : Config) (expression : Expr) (depth : Nat) :
    ExpandM (Option Step) := do
  unless enabled config do return none
  let some helper ← helperValue? expression | return none
  let expanded ← unfoldHelper expression helper config depth
  return some { expression := expanded, helper := expression }

-- A helper can expose a higher-order beta redex, for example
-- `apply (fun x => x + x) largeArgument`. Check that substitution as well as
-- the initial delta-beta step; otherwise its duplicated arguments evade the
-- node budget. Original helper-free structural reduction stays unchanged.
/-- Reduce a helper-origin head while charging substitutions before constructing
their results. Lets remain intact for evidence scoping; named Problem containers
are never unfolded. Before any helper step, use the supplied structural reducer.
Consumers with mixed native/helper branches call this only on helper-origin
subtrees and use their original reducer on untouched native siblings. -/
partial def reduceChecked (source : Expr) (reduce : Expr → Bool → MetaM Expr)
    (bounds : Config) : ExpandM Expr := do
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
      -- Select only an exposed constructor. Named container definitions must
      -- go through bounded helper unfolding, never unrestricted whnf.
      let problem ← reduceChecked arguments[2]! reduce bounds
      if let .letE name type value body nondep := problem then
        -- Keep container-local proofs and instances in scope around the field.
        let inner := (arguments.map (·.liftLooseBVars 0 1)).set! 2 body
        return .letE name type value (mkAppN function inner) nondep
      if problem.isAppOfArity ``Morew.Problem.mk 4 then
        let index := if function.isConstOf ``Morew.Problem.objective then 2 else 3
        return ← reduceChecked (mkAppN problem.getAppArgs[index]!
          (arguments.extract 3 arguments.size)) reduce bounds
      return mkAppN function (arguments.set! 2 problem)
    return mkAppN function arguments
  | _ => return expression

end Morew.Elab.Expansion
