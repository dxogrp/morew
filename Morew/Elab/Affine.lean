/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Affine
import Morew.Elab.Affine.Space
import Morew.Elab.Affine.State
import Morew.Elab.Affine.Expansion
import Morew.Core
import Mathlib.Tactic.NormNum
import Lean.Meta.Check
import Lean.Meta.Match.MatcherInfo

/-!
# Typed, proof-producing affine reification

This internal API recognizes a bounded fragment of elaborated real arithmetic.
It builds ordinary affine maps and pointwise proofs without rewriting models.
When direct recognition fails, bounded expansion of transparent helper definitions
can expose supported arithmetic. Failure means that this fragment did not certify
the expression, not that the function is mathematically non-affine.
-/

namespace Morew.Elab.Affine

open Lean Lean.Meta Qq

/-- An unsupported expression together with a diagnostic retaining its context. -/
structure AffineError where
  /-- The smallest expression at which recognition failed. -/
  expression : Expr
  /-- Explanation, including the pretty-printing context of the expression. -/
  reason : MessageData

instance : ToMessageData AffineError := ⟨(·.reason)⟩

/-- Optional proof provision for the deliberately restricted division rule. -/
structure Config where
  /-- Given the proposition `c ≠ 0`, optionally supply a checked proof. -/
  nonzeroEvidence? : Option (Expr → MetaM (Option Expr)) := none

/-- A real affine map and its pointwise agreement with the supplied function. -/
structure AffineResult where
  /-- An expression of type `X →ᵃ[ℝ] Y`. -/
  map : Expr
  /-- A proof of `∀ x, map x = source x`. -/
  pointwiseEquality : Expr

private abbrev ReifyM := ExceptT AffineError MetaM

private def reject (expression : Expr) (reason : MessageData) : ReifyM α := do
  throwThe AffineError {
    expression
    reason := ← addMessageContext
      m!"cannot certify affine expression {expression}: {reason}"
  }

-- Follow local declaration values AND types. Merely checking `hasFVar` on a
-- coefficient misses dependencies hidden behind a local let or an instance.
private partial def inspectLocals (expression : Expr) (point? : Option FVarId)
    (seen : FVarIdSet := {}) : MetaM (Bool × Bool) := do
  let expression ← instantiateMVars expression
  let mut dependent := false
  let mut unresolved := expression.hasMVar
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    if point? == some id then dependent := true
    unless seen.contains id do
      seen := seen.insert id
      if let some declaration := (← getLCtx).find? id then
        let (dep, hole) ← inspectLocals declaration.type point? seen
        dependent := dependent || dep
        unresolved := unresolved || hole
        if let some value := declaration.value? (allowNondep := true) then
          let (dep, hole) ← inspectLocals value point? seen
          dependent := dependent || dep
          unresolved := unresolved || hole
  return (dependent, unresolved)

/-- Whether an expression depends on the decision free variable, following
local declaration values and types as well as resolved metavariables. -/
def depends (point expression : Expr) : MetaM Bool := do
  return (← inspectLocals expression (some point.fvarId!)).1

/-- Reduce local lets, applications, projections, and compiler-generated tuple
matches while preserving named arithmetic and user function heads.

Only problem-container fields and single-alternative product matchers may
unfold named declarations. This is internal support for typed presentations.
With `preserveLets`, stop at a head let so the caller can retain its evidence
and local instances while recognizing the body.
-/
partial def reduceStructure (expression : Expr) (preserveLets : Bool := false) :
    MetaM Expr := do
  let expression := (← instantiateMVars expression).consumeMData
  match expression with
  | .letE _ _ value body _ =>
    if preserveLets then pure expression
    else reduceStructure (body.instantiate1 value)
  | .fvar id =>
    if let some value := (← id.getDecl).value? (allowNondep := true) then
      reduceStructure value preserveLets
    else pure expression
  | .proj name index value =>
    let value ← reduceStructure value preserveLets
    if value.isAppOf ``Prod.mk then
      reduceStructure value.getAppArgs[index + 2]! preserveLets
    else pure (.proj name index value)
  | .app .. =>
    let arguments := expression.getAppArgs
    let function ← reduceStructure expression.getAppFn preserveLets
    if let .letE name type value body nondep := function then
      return ← reduceStructure (.letE name type value
        (mkAppN body (arguments.map (·.liftLooseBVars 0 1))) nondep) preserveLets
    if function.isLambda then
      return ← reduceStructure (function.beta arguments) preserveLets
    if (function.isConstOf ``Prod.casesOn || function.isConstOf ``Prod.rec) &&
        arguments.size >= 5 then
      let value := arguments[if function.isConstOf ``Prod.casesOn then 3 else 4]!
      let branch := arguments[if function.isConstOf ``Prod.casesOn then 4 else 3]!
      let fields := #[Expr.proj ``Prod 0 value, Expr.proj ``Prod 1 value]
      return ← reduceStructure (mkAppN (branch.beta fields)
        (arguments.extract 5 arguments.size)) preserveLets
    if let some name := function.constName? then
      if let some matcher ← getMatcherInfo? name then
        if matcher.numAlts == 1 && arguments.size >= matcher.arity then
          let mut productsOnly := decide (matcher.numDiscrs > 0)
          for i in [matcher.getFirstDiscrPos:matcher.getFirstAltPos] do
            let type ← whnf (← inferType arguments[i]!)
            productsOnly := productsOnly && type.isAppOfArity ``Prod 2
          if productsOnly then
            let declaration ← getConstInfo name
            if let some value := declaration.value? then
              let value := value.instantiateLevelParams
                declaration.levelParams function.constLevels!
              return ← reduceStructure (value.beta arguments) preserveLets
    if (function.isConstOf ``Prod.fst || function.isConstOf ``Prod.snd) &&
        arguments.size >= 3 then
      let projection := .proj ``Prod
        (if function.isConstOf ``Prod.fst then 0 else 1) arguments[2]!
      return ← reduceStructure (mkAppN projection (arguments.extract 3 arguments.size))
        preserveLets
    if (function.isConstOf ``Morew.Problem.objective ||
        function.isConstOf ``Morew.Problem.feasible) && arguments.size >= 3 then
      -- The model declaration is the container being inspected; its objective
      -- and constraint function heads remain intact after selecting the field.
      let problem ← whnf arguments[2]!
      if problem.isAppOf ``Morew.Problem.mk then
        let index := if function.isConstOf ``Morew.Problem.objective then 2 else 3
        return ← reduceStructure (mkAppN problem.getAppArgs[index]!
          (arguments.extract 3 arguments.size)) preserveLets
    return mkAppN function arguments
  | _ => pure expression

/-- Whether a type has the supported real/Euclidean/product/finite-function shape. -/
partial def isSupportedSpace (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isConstOf ``Real then return true
  if (← Space.euclideanDimension? type).isSome then return true
  if type.isAppOfArity ``Prod 2 then
    return (← isSupportedSpace type.getAppArgs[0]!) &&
      (← isSupportedSpace type.getAppArgs[1]!)
  if let .forallE _ index body _ := type then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars || (← isProp index) then return false
    -- Shape validation needs finiteness, not an enumeration in the ambient
    -- context. Indexed operations retain their own elaborated Fintype instance.
    let finiteType ← mkAppM ``Finite #[index]
    unless (← synthInstance? finiteType).isSome do return false
    return ← isSupportedSpace body
  return false

/-- Recover finiteness proofs from `Finite` evidence and `Fintype` indexing
instances already present in the typed source. Local lets are substituted, but
named helpers are not expanded.
Instances mentioning a source binder are never promoted into the caller's scope.
Only `Finite` proofs are collected: each operation keeps its own enumeration. -/
def sourceFiniteInstances (source : Expr) : MetaM (Array Expr) := do
  let mut pending := [source]
  let mut seen : ExprSet := {}
  let mut instances := #[]
  while let expression :: rest := pending do
    pending := rest
    if seen.contains expression then continue
    seen := seen.insert expression
    let expression ← if expression.hasLooseBVars then
        pure expression.consumeMData.headBeta
      else reduceStructure expression (preserveLets := true)
    unless expression.hasLooseBVars do
      -- Inspect the elaborated type rather than operation names or the spelling
      -- of a let annotation. This also handles aliased classes and coefficients
      -- such as Fintype.card, without expanding their definitions.
      let type ← whnf (← inferType expression)
      if type.isAppOfArity ``Finite 1 then
        unless instances.contains expression do
          instances := instances.push expression
      else if type.isAppOfArity ``Fintype 1 then
        let proof ← mkAppOptM ``Finite.of_fintype
          #[some type.getAppArgs[0]!, some expression]
        unless instances.contains proof do
          instances := instances.push proof
    match expression with
    | .letE _ _ value body _ => pending := value :: body.instantiate1 value :: pending
    | .lam _ _ body _ | .forallE _ _ body _ => pending := body :: pending
    | .app f a => pending := f :: a :: pending
    | .proj _ _ value => pending := value :: pending
    | .mdata _ value => pending := value :: pending
    | _ => pure ()
  return instances

/-- Discover additional finite-index evidence hidden in transparent value helpers.
This is used only after a direct certification attempt fails. It never changes
the predicate or objective retained by the caller. -/
def helperFiniteInstances (source : Expr) : MetaM (Array Expr) := do
  unless ← Expansion.enabled do return #[]
  let prepared ← Expansion.prepare source (fun expression preserve => reduceStructure expression preserve)
  if prepared.expansions == 0 then return #[]
  let original ← sourceFiniteInstances source
  return (← sourceFiniteInstances prepared.expression).filter (!original.contains ·)

private def withFiniteInstances (instances : List Expr) (action : ReifyM Expr) :
    ReifyM Expr := do
  match instances with
  | [] => action
  | inst :: rest =>
    mapLetDeclZeta `_sourceFinite (← inferType inst) inst fun _ =>
      withFiniteInstances rest action

private def functionOf (point body : Expr) : MetaM Expr :=
  mkLambdaFVars #[point] body

private def certifiedFunction (certificate : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← inferType certificate)
  unless type.isAppOf ``Morew.Affine.Certified do
    throwError "internal affine constructor returned an unexpected type"
  return type.getAppArgs.back!

-- Compare the operation prefix independently of the actual operands. A
-- nonstandard operation could coincide with the standard one on these operands.
private def checkPrefix (source expected : Expr) (operandCount : Nat) : ReifyM Unit := do
  let source := source.consumeMData
  let expected ← reduceStructure expected
  let sourceArgs := source.getAppArgs
  let expectedArgs := expected.getAppArgs
  unless source.getAppFn == expected.getAppFn &&
      sourceArgs.size == expectedArgs.size && operandCount ≤ sourceArgs.size do
    reject source "unsupported operation or arithmetic instance"
  let prefixSize := sourceArgs.size - operandCount
  for i in [:prefixSize] do
    unless ← isDefEq sourceArgs[i]! expectedArgs[i]! do
      reject source "unsupported arithmetic instance; expected the canonical real operation"

private def finish (point source certificate : Expr)
    (operandCount? : Option Nat := none) : ReifyM Expr := do
  let function ← certifiedFunction certificate
  if let some count := operandCount? then
    checkPrefix source (function.beta #[point]) count
  unless ← isDefEq function (← functionOf point source) do
    reject source "the supported affine construction does not match this typed expression"
  return certificate

private def withIndexInstance (point inst : Expr) (action : ReifyM Expr) : ReifyM Expr := do
  if ← depends point inst then
    reject inst "the finite indexing instance depends on a decision variable"
  mapLetDeclZeta `_affineIndex (← inferType inst) inst fun _ => action

private def construct (point source : Expr) (name : Name) (args : Array Expr)
    (operandCount? : Option Nat := none) : ReifyM Expr := do
  let certificate ← try
    let spaces := #[← inferType point, ← inferType source]
    Space.withCanonicalSpaces spaces do
      let mut term ← mkAppM name args
      repeat
        let type ← whnf (← inferType term)
        if let .forallE _ domain _ .instImplicit := type then
          term := mkApp term (← synthInstance domain)
        else break
      pure term
  catch exception =>
    reject source m!"unsupported types or instances: {exception.toMessageData}"
  finish point source certificate operandCount?

private def nonzeroProof (point divisor : Expr) (config : Config) : ReifyM Expr := do
  if ← depends point divisor then
    reject divisor "the divisor depends on a decision variable"
  let zero : Expr := q((0 : ℝ))
  let obligation ← mkAppM ``Ne #[divisor, zero]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if ← isDefEq declaration.type obligation then
        let (dependent, unresolved) ← inspectLocals declaration.toExpr (some point.fvarId!)
        if dependent then
          reject divisor "nonzero evidence depends on the decision point"
        if unresolved then
          reject divisor "nonzero evidence contains unresolved metavariables"
        return declaration.toExpr
  if let some provide := config.nonzeroEvidence? then
    if let some proof ← provide obligation then
      unless ← isDefEq (← inferType proof) obligation do
        reject divisor "supplied evidence does not prove that the divisor is nonzero"
      let (dependent, unresolved) ← inspectLocals proof (some point.fvarId!)
      if dependent then
        reject divisor "nonzero evidence depends on the decision point"
      if unresolved then
        reject divisor "nonzero evidence contains unresolved metavariables"
      return proof
  try
    -- Keep automatic numeral/rational evidence generation bounded even if the
    -- surrounding command has disabled its global heartbeat limit. Preserve a
    -- tighter caller limit and the caller's original heartbeat origin.
    let context ← readThe Core.Context
    let localLimit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
    let limit := if context.maxHeartbeats == 0 then localLimit
      else min context.maxHeartbeats localLimit
    let result ← withTheReader Core.Context
      (fun context => { context with maxHeartbeats := limit }) <|
      Mathlib.Meta.NormNum.deriveBool obligation
    match result with
    | ⟨true, proof⟩ => return proof
    | ⟨false, _⟩ => pure ()
  catch _ => pure ()
  reject divisor m!"missing nonzero evidence; required {obligation}"

private partial def reifyBody (point expression : Expr) (config : Config) : ReifyM Expr := do
  let expression ← reduceStructure expression (preserveLets := true)
  if let .letE name type value body nondep := expression then
    -- A local alias of the decision point must be substituted before building
    -- a new function binder. Independent lets retain useful proof/instance scope.
    if (← depends point type) || (← depends point value) then
      return ← reifyBody point (body.instantiate1 value) config
    return ← mapLetDeclZeta name type value (nondep := nondep) fun binding =>
      reifyBody point (body.instantiate1 binding) config
  let type ← inferType expression
  unless ← isSupportedSpace type do
    reject expression m!"unsupported affine value type {type}"
  let domain ← inferType point
  if !(← depends point expression) then
    return ← construct point expression ``Morew.Affine.Certified.const #[domain, expression]
  if expression == point then
    return ← construct point expression ``Morew.Affine.Certified.id #[domain]
  if let .proj ``WithLp 0 value := expression then
    if (← Space.euclideanDimension? (← inferType value)).isSome then
      let value ← reifyBody point value config
      return ← construct point expression ``Morew.Affine.Certified.ofEuclidean #[value]
  if let .proj ``Prod index value := expression then
    let value ← reifyBody point value config
    let constructor := if index == 0 then
      ``Morew.Affine.Certified.fst else ``Morew.Affine.Certified.snd
    return ← construct point expression constructor #[value]
  if let .lam name index body info := expression then
    let family ← withLocalDecl name info index fun i => do
      let certificate ← reifyBody point (body.instantiate1 i) config
      mkLambdaFVars #[i] certificate
    return ← construct point expression ``Morew.Affine.Certified.pi #[family]
  let head := expression.getAppFn
  let args := expression.getAppArgs
  let name := head.constName?
  if name == some ``WithLp.toLp && args.size == 3 then
    if (← Space.euclideanDimension? type).isSome then
      let value ← reifyBody point args[2]! config
      return ← construct point expression ``Morew.Affine.Certified.toEuclidean #[value]
  if name == some ``WithLp.ofLp && args.size == 3 then
    if (← Space.euclideanDimension? (← inferType args[2]!)).isSome then
      let value ← reifyBody point args[2]! config
      return ← construct point expression ``Morew.Affine.Certified.ofEuclidean #[value]
  if name == some ``HAdd.hAdd && args.size == 6 then
    let left ← reifyBody point args[4]! config
    let right ← reifyBody point args[5]! config
    return ← construct point expression ``Morew.Affine.Certified.add #[left, right] (some 2)
  if name == some ``HSub.hSub && args.size == 6 then
    let left ← reifyBody point args[4]! config
    let right ← reifyBody point args[5]! config
    return ← construct point expression ``Morew.Affine.Certified.sub #[left, right] (some 2)
  if name == some ``Neg.neg && args.size == 3 then
    let value ← reifyBody point args[2]! config
    return ← construct point expression ``Morew.Affine.Certified.neg #[value] (some 1)
  if name == some ``HMul.hMul && args.size == 6 then
    let left := args[4]!
    let right := args[5]!
    if !(← depends point left) then
      let rightMap ← reifyBody point right config
      return ← construct point expression ``Morew.Affine.Certified.mulConstLeft
        #[left, rightMap] (some 2)
    if !(← depends point right) then
      let leftMap ← reifyBody point left config
      return ← construct point expression ``Morew.Affine.Certified.mulConstRight
        #[leftMap, right] (some 2)
    discard <| reifyBody point left config
    discard <| reifyBody point right config
    reject expression "both factors of multiplication depend on decision variables"
  if name == some ``HSMul.hSMul && args.size == 6 then
    let coefficient := args[4]!
    if ← depends point coefficient then
      if !(← depends point args[5]!) && (← isDefEq type (mkConst ``Real)) &&
          (← isDefEq (← inferType coefficient) (mkConst ``Real)) then
        let scalar ← reifyBody point coefficient config
        return ← construct point expression ``Morew.Affine.Certified.smulConst
          #[scalar, args[5]!] (some 2)
      reject coefficient "the scalar coefficient depends on a decision variable"
    let value ← reifyBody point args[5]! config
    let scalarType ← inferType coefficient
    let constructor ← if ← isDefEq scalarType (mkConst ``Real) then
        pure ``Morew.Affine.Certified.realSMul
      else if ← isDefEq scalarType (mkConst ``Nat) then
        pure ``Morew.Affine.Certified.natSMul
      else reject coefficient "only real and natural scalar coefficients are supported"
    return ← construct point expression constructor #[coefficient, value] (some 2)
  if name == some ``HDiv.hDiv && args.size == 6 then
    let numerator ← reifyBody point args[4]! config
    let proof ← nonzeroProof point args[5]! config
    return ← construct point expression ``Morew.Affine.Certified.divConst
      #[numerator, args[5]!, proof] (some 2)
  if name == some ``HPow.hPow && args.size == 6 then
    let exponent ← reduceStructure args[5]!
    if ← isDefEq (← inferType exponent) (mkConst ``Nat) then
      if (← getNatValue? exponent) == some 0 then
        let source ← functionOf point args[4]!
        return ← construct point expression ``Morew.Affine.Certified.powZeroSource
          #[source] (some 2)
      if (← getNatValue? exponent) == some 1 then
        let base ← reifyBody point args[4]! config
        return ← construct point expression ``Morew.Affine.Certified.powOne #[base] (some 2)
    reject expression "a decision-dependent power is supported only with natural exponent 0 or 1"
  if name == some ``Prod.mk && args.size == 4 then
    let left ← reifyBody point args[2]! config
    let right ← reifyBody point args[3]! config
    return ← construct point expression ``Morew.Affine.Certified.pair #[left, right]
  if name == some ``Matrix.vecCons && args.size == 4 then
    let first ← reifyBody point args[2]! config
    let rest ← reifyBody point args[3]! config
    return ← construct point expression ``Morew.Affine.Certified.vecCons #[first, rest]
  if name == some ``Finset.sum && args.size == 5 then
    let set := args[3]!
    if ← depends point set then
      reject set "the finite sum's index set depends on a decision variable"
    let family ← withLocalDeclD `i args[0]! fun i => do
      let certificate ← reifyBody point (mkApp args[4]! i) config
      mkLambdaFVars #[i] certificate
    return ← construct point expression ``Morew.Affine.Certified.sum #[set, family] (some 2)
  if name == some ``dotProduct && args.size == 7 then
    return ← withIndexInstance point args[2]! do
      let left := args[5]!
      let right := args[6]!
      if !(← depends point left) then
        let rightMap ← reifyBody point right config
        return ← construct point expression ``Morew.Affine.Certified.dotConstLeft
          #[left, rightMap] (some 2)
      if !(← depends point right) then
        let leftMap ← reifyBody point left config
        return ← construct point expression ``Morew.Affine.Certified.dotConstRight
          #[leftMap, right] (some 2)
      discard <| reifyBody point left config
      discard <| reifyBody point right config
      reject expression "both dot-product factors depend on decision variables"
  if (name == some ``Matrix.mulVec || name == some ``Matrix.vecMul) && args.size == 7 then
    return ← withIndexInstance point args[4]! do
      let matrix := if name == some ``Matrix.mulVec then args[5]! else args[6]!
      let vector := if name == some ``Matrix.mulVec then args[6]! else args[5]!
      if ← depends point matrix then
        -- Diagnose an unsupported entry first, then the coefficient's dependence.
        discard <| reifyBody point matrix config
        reject matrix "the coefficient matrix depends on a decision variable"
      let vectorMap ← reifyBody point vector config
      if name == some ``Matrix.mulVec then
        return ← construct point expression ``Morew.Affine.Certified.mulVec
          #[matrix, vectorMap] (some 2)
      return ← construct point expression ``Morew.Affine.Certified.vecMul
        #[vectorMap, matrix] (some 2)
  -- A finite vector can be evaluated at a fixed index. This is deliberately
  -- checked after recognized operation heads so it cannot swallow a nonlinear
  -- function application under the guise of a projection.
  if let .app vector index := expression then
    let vectorType ← whnf (← inferType vector)
    if vectorType.isForall && (← isSupportedSpace vectorType) then
      if ← depends point index then
        reject index "the vector index depends on a decision variable"
      let vectorMap ← reifyBody point vector config
      return ← construct point expression ``Morew.Affine.Certified.eval #[vectorMap, index]
  -- Prefer a failing inner operand to its enclosing unsupported application.
  for argument in args do
    if (← depends point argument) && (← isSupportedSpace (← inferType argument)) then
      discard <| reifyBody point argument config
  reject expression "unsupported function, coercion, or nonlinear operation"

private def reifyCore (source : Expr) (config : Config)
    (original? : Option Expr := none) : ReifyM AffineResult := do
  let source ← instantiateMVars source
  if (← inspectLocals source none).2 then
    reject source "unresolved metavariables are not supported"
  let type ← whnf (← inferType source)
  let .forallE _ domain codomain _ := type
    | reject source "expected a function from a decision space"
  if codomain.hasLooseBVars then
    reject source "dependent result types are not supported"
  let original := original?.getD source
  let instances ← sourceFiniteInstances source
  let originalInstances ← if original?.isSome then sourceFiniteInstances original else pure #[]
  let certificate ← withFiniteInstances (instances ++ originalInstances).toList do
    unless ← isSupportedSpace domain do
      reject source m!"unsupported decision space {domain}"
    withLocalDeclD `point domain fun point => do
      reifyBody point (mkApp source point) config
  let map ← mkProjection certificate `map
  let equality ← mkProjection certificate `correct
  let map ← instantiateMVars map
  let equality ← instantiateMVars equality
  if map.hasMVar || equality.hasMVar then
    reject source "affine construction left unresolved metavariables"
  let expected ← withLocalDeclD `point domain fun point => do
    let value := mkApp (← mkProjection map `toFun) point
    mkForallFVars #[point] (← mkEq value (mkApp original point))
  unless ← isDefEq (← inferType equality) expected do
    reject source "affine certificate does not establish equality to the original function"
  checkWithKernel map
  checkWithKernel equality
  return { map, pointwiseEquality := equality }

/-- Reify a typed function without modifying caller metavariables.

All success results contain ordinary proof terms checked against the original
function. Transparent helpers are expanded only in a temporary expression after
direct recognition fails. The optional evidence callback is checked against
`c ≠ 0`; it does not weaken the global pointwise correctness obligation.
-/
def reifyAffine (source : Expr) (config : Config := {}) :
    MetaM (Except AffineError AffineResult) := withIsolatedMVars do
  try
    let direct ← withIsolatedMVars <| (reifyCore source config).run
    if let .ok result := direct then return .ok result
    unless ← Expansion.enabled do return direct
    -- Do not expand an incompletely elaborated term or allow expansion to
    -- discard an unresolved argument before the original input is checked.
    if (← inspectLocals source none).2 then return direct
    let prepared ← Expansion.prepare source (fun expression preserve => reduceStructure expression preserve)
    if prepared.expansions == 0 then return direct
    match ← (reifyCore prepared.expression config (some source)).run with
    | .ok result => return .ok result
    | .error error => return .error { error with
        reason := ← addMessageContext
          m!"while expanding affine helpers in {source}: {error.reason}" }
  catch exception =>
    return .error {
      expression := source
      reason := ← addMessageContext exception.toMessageData
    }

end Morew.Elab.Affine
