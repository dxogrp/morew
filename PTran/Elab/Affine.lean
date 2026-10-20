import PTran.Affine
import PTran.Elab.Affine.Space
import PTran.Core
import Mathlib.Tactic.NormNum
import Lean.Meta.Check
import Lean.Meta.Match.MatcherInfo

/-!
# Typed, proof-producing affine reification

This internal API recognizes a bounded fragment of elaborated real arithmetic.
It builds ordinary affine maps and pointwise proofs, without rewriting models
or expanding named user functions. Failure means that this fragment did not
certify the expression, not that the function is mathematically non-affine.
-/

namespace PTran.Elab.Affine

open Lean Lean.Meta

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

private def depends (point expression : Expr) : MetaM Bool := do
  return (← inspectLocals expression (some point.fvarId!)).1

/-- Reduce local lets, applications, projections, and compiler-generated tuple
matches while preserving named arithmetic and user function heads.

Only problem-container fields and single-alternative product matchers may
unfold named declarations. This is internal support for typed presentations.
-/
partial def reduceStructure (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData
  match expression with
  | .letE _ _ value body _ => reduceStructure (body.instantiate1 value)
  | .fvar id =>
    if let some value := (← id.getDecl).value? (allowNondep := true) then
      reduceStructure value
    else pure expression
  | .proj name index value =>
    let value ← reduceStructure value
    if value.isAppOf ``Prod.mk then
      reduceStructure value.getAppArgs[index + 2]!
    else pure (.proj name index value)
  | .app .. =>
    let arguments := expression.getAppArgs
    let function ← reduceStructure expression.getAppFn
    if function.isLambda then
      return ← reduceStructure (function.beta arguments)
    if (function.isConstOf ``Prod.casesOn || function.isConstOf ``Prod.rec) &&
        arguments.size >= 5 then
      let value := arguments[if function.isConstOf ``Prod.casesOn then 3 else 4]!
      let branch := arguments[if function.isConstOf ``Prod.casesOn then 4 else 3]!
      let fields := #[Expr.proj ``Prod 0 value, Expr.proj ``Prod 1 value]
      return ← reduceStructure <| mkAppN (branch.beta fields)
        (arguments.extract 5 arguments.size)
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
              return ← reduceStructure (value.beta arguments)
    if (function.isConstOf ``Prod.fst || function.isConstOf ``Prod.snd) &&
        arguments.size >= 3 then
      let projection := .proj ``Prod
        (if function.isConstOf ``Prod.fst then 0 else 1) arguments[2]!
      return ← reduceStructure <| mkAppN projection (arguments.extract 3 arguments.size)
    if (function.isConstOf ``PTran.Problem.objective ||
        function.isConstOf ``PTran.Problem.feasible) && arguments.size >= 3 then
      -- The model declaration is the container being inspected; its objective
      -- and constraint function heads remain intact after selecting the field.
      let problem ← whnf arguments[2]!
      if problem.isAppOf ``PTran.Problem.mk then
        let index := if function.isConstOf ``PTran.Problem.objective then 2 else 3
        return ← reduceStructure <| mkAppN problem.getAppArgs[index]!
          (arguments.extract 3 arguments.size)
    return mkAppN function arguments
  | _ => pure expression

/-- Whether a type has the supported real/product/finite-function shape. -/
partial def isSupportedSpace (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isConstOf ``Real then return true
  if type.isAppOfArity ``Prod 2 then
    return (← isSupportedSpace type.getAppArgs[0]!) &&
      (← isSupportedSpace type.getAppArgs[1]!)
  if let .forallE _ index body _ := type then
    if body.hasLooseBVars then return false
    let finiteType ← mkAppM ``Fintype #[index]
    unless (← synthInstance? finiteType).isSome do return false
    return ← isSupportedSpace body
  return false

private def functionOf (point body : Expr) : MetaM Expr :=
  mkLambdaFVars #[point] body

private def certifiedFunction (certificate : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← inferType certificate)
  unless type.isAppOf ``PTran.Affine.Certified do
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

private def withIndexInstances (instances : List Expr) (action : MetaM Expr) : MetaM Expr := do
  match instances with
  | [] => action
  | inst :: rest =>
    mapLetDeclZeta `_affineIndex (← inferType inst) inst fun _ =>
      withIndexInstances rest action

private def construct (point source : Expr) (name : Name) (args : Array Expr)
    (operandCount? : Option Nat := none) (indexInstances : Array Expr := #[]) :
    ReifyM Expr := do
  for inst in indexInstances do
    if ← depends point inst then
      reject inst "the finite indexing instance depends on a decision variable"
  let certificate ← try
    let spaces := #[← inferType point, ← inferType source]
    withIndexInstances indexInstances.toList <| Space.withCanonicalSpaces spaces do
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
  let zero ← mkNumeral (mkConst ``Real) 0
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
  let expression ← reduceStructure expression
  let type ← inferType expression
  unless ← isSupportedSpace type do
    reject expression m!"unsupported affine value type {type}"
  let domain ← inferType point
  if !(← depends point expression) then
    return ← construct point expression ``PTran.Affine.Certified.const #[domain, expression]
  if expression == point then
    return ← construct point expression ``PTran.Affine.Certified.id #[domain]
  if let .proj ``Prod index value := expression then
    let value ← reifyBody point value config
    let constructor := if index == 0 then
      ``PTran.Affine.Certified.fst else ``PTran.Affine.Certified.snd
    return ← construct point expression constructor #[value]
  if let .lam name index body info := expression then
    let family ← withLocalDecl name info index fun i => do
      let certificate ← reifyBody point (body.instantiate1 i) config
      mkLambdaFVars #[i] certificate
    return ← construct point expression ``PTran.Affine.Certified.pi #[family]
  let head := expression.getAppFn
  let args := expression.getAppArgs
  let name := head.constName?
  if name == some ``HAdd.hAdd && args.size == 6 then
    let left ← reifyBody point args[4]! config
    let right ← reifyBody point args[5]! config
    return ← construct point expression ``PTran.Affine.Certified.add #[left, right] (some 2)
  if name == some ``HSub.hSub && args.size == 6 then
    let left ← reifyBody point args[4]! config
    let right ← reifyBody point args[5]! config
    return ← construct point expression ``PTran.Affine.Certified.sub #[left, right] (some 2)
  if name == some ``Neg.neg && args.size == 3 then
    let value ← reifyBody point args[2]! config
    return ← construct point expression ``PTran.Affine.Certified.neg #[value] (some 1)
  if name == some ``HMul.hMul && args.size == 6 then
    let left := args[4]!
    let right := args[5]!
    if !(← depends point left) then
      let rightMap ← reifyBody point right config
      return ← construct point expression ``PTran.Affine.Certified.mulConstLeft
        #[left, rightMap] (some 2)
    if !(← depends point right) then
      let leftMap ← reifyBody point left config
      return ← construct point expression ``PTran.Affine.Certified.mulConstRight
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
        return ← construct point expression ``PTran.Affine.Certified.smulConst
          #[scalar, args[5]!] (some 2)
      reject coefficient "the scalar coefficient depends on a decision variable"
    let value ← reifyBody point args[5]! config
    let scalarType ← inferType coefficient
    let constructor ← if ← isDefEq scalarType (mkConst ``Real) then
        pure ``PTran.Affine.Certified.realSMul
      else if ← isDefEq scalarType (mkConst ``Nat) then
        pure ``PTran.Affine.Certified.natSMul
      else reject coefficient "only real and natural scalar coefficients are supported"
    return ← construct point expression constructor #[coefficient, value] (some 2)
  if name == some ``HDiv.hDiv && args.size == 6 then
    let numerator ← reifyBody point args[4]! config
    let proof ← nonzeroProof point args[5]! config
    return ← construct point expression ``PTran.Affine.Certified.divConst
      #[numerator, args[5]!, proof] (some 2)
  if name == some ``HPow.hPow && args.size == 6 then
    let exponent ← reduceStructure args[5]!
    if ← isDefEq (← inferType exponent) (mkConst ``Nat) then
      if (← getNatValue? exponent) == some 0 then
        let source ← functionOf point args[4]!
        return ← construct point expression ``PTran.Affine.Certified.powZeroSource
          #[source] (some 2)
      if (← getNatValue? exponent) == some 1 then
        let base ← reifyBody point args[4]! config
        return ← construct point expression ``PTran.Affine.Certified.powOne #[base] (some 2)
    reject expression "a decision-dependent power is supported only with natural exponent 0 or 1"
  if name == some ``Prod.mk && args.size == 4 then
    let left ← reifyBody point args[2]! config
    let right ← reifyBody point args[3]! config
    return ← construct point expression ``PTran.Affine.Certified.pair #[left, right]
  if name == some ``Matrix.vecCons && args.size == 4 then
    let first ← reifyBody point args[2]! config
    let rest ← reifyBody point args[3]! config
    return ← construct point expression ``PTran.Affine.Certified.vecCons #[first, rest]
  if name == some ``Finset.sum && args.size == 5 then
    let set := args[3]!
    if ← depends point set then
      reject set "the finite sum's index set depends on a decision variable"
    let family ← withLocalDeclD `i args[0]! fun i => do
      let certificate ← reifyBody point (mkApp args[4]! i) config
      mkLambdaFVars #[i] certificate
    return ← construct point expression ``PTran.Affine.Certified.sum #[set, family] (some 2)
  if name == some ``dotProduct && args.size == 7 then
    let left := args[5]!
    let right := args[6]!
    if !(← depends point left) then
      let rightMap ← reifyBody point right config
      return ← construct point expression ``PTran.Affine.Certified.dotConstLeft
        #[left, rightMap] (some 2) #[args[2]!]
    if !(← depends point right) then
      let leftMap ← reifyBody point left config
      return ← construct point expression ``PTran.Affine.Certified.dotConstRight
        #[leftMap, right] (some 2) #[args[2]!]
    discard <| reifyBody point left config
    discard <| reifyBody point right config
    reject expression "both dot-product factors depend on decision variables"
  if (name == some ``Matrix.mulVec || name == some ``Matrix.vecMul) && args.size == 7 then
    let matrix := if name == some ``Matrix.mulVec then args[5]! else args[6]!
    let vector := if name == some ``Matrix.mulVec then args[6]! else args[5]!
    if ← depends point matrix then
      -- Diagnose an unsupported entry first, then the coefficient's dependence.
      discard <| reifyBody point matrix config
      reject matrix "the coefficient matrix depends on a decision variable"
    let vectorMap ← reifyBody point vector config
    if name == some ``Matrix.mulVec then
      return ← construct point expression ``PTran.Affine.Certified.mulVec
        #[matrix, vectorMap] (some 2) #[args[4]!]
    return ← construct point expression ``PTran.Affine.Certified.vecMul
      #[vectorMap, matrix] (some 2) #[args[4]!]
  -- A finite vector can be evaluated at a fixed index. This is deliberately
  -- checked after recognized operation heads so it cannot swallow a nonlinear
  -- function application under the guise of a projection.
  if let .app vector index := expression then
    let vectorType ← whnf (← inferType vector)
    if vectorType.isForall && (← isSupportedSpace vectorType) then
      if ← depends point index then
        reject index "the vector index depends on a decision variable"
      let vectorMap ← reifyBody point vector config
      return ← construct point expression ``PTran.Affine.Certified.eval #[vectorMap, index]
  -- Prefer a failing inner operand to its enclosing unsupported application.
  for argument in args do
    if (← depends point argument) && (← isSupportedSpace (← inferType argument)) then
      discard <| reifyBody point argument config
  reject expression "unsupported function, coercion, or nonlinear operation"

private def reifyCore (source : Expr) (config : Config) : ReifyM AffineResult := do
  if (← inspectLocals source none).2 then
    reject source "unresolved metavariables are not supported"
  let type ← whnf (← inferType source)
  let .forallE _ domain codomain _ := type
    | reject source "expected a function from a decision space"
  if codomain.hasLooseBVars then
    reject source "dependent result types are not supported"
  unless ← isSupportedSpace domain do
    reject source m!"unsupported decision space {domain}"
  let certificate ← withLocalDeclD `point domain fun point => do
    reifyBody point (mkApp source point) config
  let map ← mkAppM ``PTran.Affine.Certified.map #[certificate]
  let equality ← mkAppM ``PTran.Affine.Certified.correct #[certificate]
  let map ← instantiateMVars map
  let equality ← instantiateMVars equality
  if map.hasMVar || equality.hasMVar then
    reject source "affine construction left unresolved metavariables"
  let expected ← withLocalDeclD `point domain fun point => do
    let value ← mkAppM ``AffineMap.toFun #[map, point]
    mkForallFVars #[point] (← mkEq value (mkApp source point))
  unless ← isDefEq (← inferType equality) expected do
    reject source "affine certificate does not establish equality to the original function"
  checkWithKernel map
  checkWithKernel equality
  return { map, pointwiseEquality := equality }

/-- Reify a typed function without modifying caller metavariables.

All success results contain ordinary proof terms. Named user function heads
are not unfolded. The optional evidence callback is checked against `c ≠ 0`;
it does not weaken the global pointwise correctness obligation.
-/
def reifyAffine (source : Expr) (config : Config := {}) :
    MetaM (Except AffineError AffineResult) := do
  let saved ← saveState
  try
    withNewMCtxDepth (reifyCore source config).run
  catch exception =>
    return .error {
      expression := source
      reason := ← addMessageContext exception.toMessageData
    }
  finally
    saved.restore

end PTran.Elab.Affine
