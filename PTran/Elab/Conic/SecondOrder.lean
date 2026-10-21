import PTran.Conic.SecondOrder
import PTran.Elab.Conic.Plan

/-!
# Checked second-order replacements

Native Euclidean and quadratic upper bounds become affine cone memberships.
Quotient rules use a positive constant margin extracted from retained rows;
their certificates are conditional on exactly those rows, in both directions.
-/

namespace PTran.Elab.Conic.SecondOrder

open Lean Lean.Meta Qq
open scoped ENNReal

/-- A same-domain replacement certified under the unchanged row conjunction. -/
structure Result where
  /-- The unchanged decision domain. -/
  domain : Expr
  /-- Generated predicates in presentation order. -/
  rowPredicates : Array Expr
  /-- Checked affine cone constraints for all generated predicates. -/
  certifiedRows : Array RowResult
  /-- `∀ x, remainder x → (source x ↔ conjunction rowPredicates x)`. -/
  conditionalIff : Expr

/-- Rebase all expressions in a contextual plan, including its domain evidence. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result := {
  domain := result.domain.replaceFVars oldVars newVars
  rowPredicates := result.rowPredicates.map (·.replaceFVars oldVars newVars)
  certifiedRows := result.certifiedRows.map fun row => {
    constraint := row.constraint.replaceFVars oldVars newVars
    pointwiseIff := row.pointwiseIff.replaceFVars oldVars newVars }
  conditionalIff := result.conditionalIff.replaceFVars oldVars newVars
}

private def conjunction (rows : Array Expr) : Expr :=
  if rows.isEmpty then mkConst ``True
  else rows.pop.toList.foldr (mkApp2 (mkConst ``And)) rows.back!

private def conjunctionParts (count : Nat) (proof : Expr) : MetaM (Array Expr) := do
  if count == 0 then return #[]
  let mut parts := #[]
  let mut rest := proof
  for _ in [:count - 1] do
    parts := parts.push (← mkAppM ``And.left #[rest])
    rest ← mkAppM ``And.right #[rest]
  return parts.push rest

private def euclidean? (type : Expr) : MetaM Bool := do
  return (← Affine.Space.euclideanDimension? type).isSome

private def operationCandidate (expression : Expr) : MetaM Bool := do
  let expression ← Affine.reduceStructure expression
  if expression.isAppOfArity ``HPow.hPow 6 || expression.isAppOfArity ``Finset.sum 5 ||
      expression.isAppOfArity ``HDiv.hDiv 6 then return true
  if expression.isAppOfArity ``Norm.norm 3 then
    return ← euclidean? expression.getAppArgs[0]!
  return false

/-- Select only the supported operation families; certification still checks
the complete relation, polarity, carrier, and operation instances. -/
def isCandidate (predicate : Expr) : MetaM Bool := do
  let saved ← saveState
  try
    if ← Plan.unresolved predicate then return false
    withNewMCtxDepth do
      let domain ← Plan.predicateDomain predicate
      withLocalDeclD `point domain fun point => do
        let body ← Affine.reduceStructure (mkApp predicate point)
        if body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``GE.ge 4 ||
            body.isAppOfArity ``Eq 3 then
          let args := body.getAppArgs
          return (← operationCandidate args[args.size - 2]!) ||
            (← operationCandidate args.back!)
        return false
  finally saved.restore

private def sameOperation (actual expected : Expr) (operands : Nat) : MetaM Unit := do
  unless actual.getAppFn == expected.getAppFn &&
      actual.getAppNumArgs == expected.getAppNumArgs do
    throwError "unsupported native operation {actual}"
  let a := actual.getAppArgs
  let b := expected.getAppArgs
  for i in [:a.size - operands] do
    unless ← isDefEq a[i]! b[i]! do
      throwError "unsupported instance in native operation {actual}"

private def sides (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← inferType proof
  unless type.isAppOfArity ``Iff 2 do throwError "internal error: expected an equivalence"
  return (type.getAppArgs[0]!, type.getAppArgs[1]!)

private def squareBase (expression : Expr) : MetaM Expr := do
  let expression ← Affine.reduceStructure expression
  unless expression.isAppOfArity ``HPow.hPow 6 do
    throwError "sum-of-squares requires a native square in each summand; found {expression}"
  let args := expression.getAppArgs
  unless (← whnf (← inferType args[5]!)).isConstOf ``Nat &&
      (← getNatValue? (← Affine.reduceStructure args[5]!)) == some 2 do
    throwError "quadratic bound requires the natural exponent 2; found {expression}"
  return args[4]!

private def positiveProof? (point epsilon : Expr) : MetaM (Option Expr) := do
  if (← Affine.depends point epsilon) || (← Plan.unresolved epsilon) then return none
  let epsilon : Q(ℝ) := epsilon
  let obligation : Q(Prop) := q(0 < $epsilon)
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if !(← Affine.depends point declaration.toExpr) &&
          !(← Plan.unresolved declaration.toExpr) &&
          (← isDefEq declaration.type obligation) then
        checkWithKernel declaration.toExpr
        return some declaration.toExpr
  try
    let context ← readThe Core.Context
    let localLimit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
    let limit := if context.maxHeartbeats == 0 then localLimit
      else min context.maxHeartbeats localLimit
    let proof ← mapLetDeclZeta `_marginOrder q(LT ℝ) q(inferInstance : LT ℝ) fun _ => do
      mapLetDeclZeta `_marginPreorder q(Preorder ℝ) q(inferInstance : Preorder ℝ) fun _ => do
      mapLetDeclZeta `_marginPartialOrder q(PartialOrder ℝ)
        q(inferInstance : PartialOrder ℝ) fun _ => do
      let result ← withTheReader Core.Context
        (fun context => { context with maxHeartbeats := limit }) <|
        Mathlib.Meta.NormNum.deriveBool obligation
      match result with
      | ⟨true, proof⟩ => pure proof
      | _ => throwError "positive margin was not established"
    checkWithKernel proof
    return some proof
  catch _ => return none

private theorem marginPositive {epsilon denominator : ℝ}
    (positive : 0 < epsilon) (bound : epsilon ≤ denominator) : 0 < denominator :=
  lt_of_lt_of_le positive bound

private partial def marginInRow? (point denominator body evidence : Expr) :
    MetaM (Option Expr) := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← marginInRow? point denominator (rest.instantiate1 value) evidence
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let proof? ← marginInRow? point denominator (rest.instantiate1 binding) evidence
      proof?.mapM fun proof => proof.replaceFVarsM #[binding] #[value]
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    if let some proof ← marginInRow? point denominator args[0]!
        (← mkAppM ``And.left #[evidence]) then return some proof
    return ← marginInRow? point denominator args[1]!
      (← mkAppM ``And.right #[evidence])
  let ge := body.isAppOfArity ``GE.ge 4
  unless ge || body.isAppOfArity ``LE.le 4 do return none
  let args := body.getAppArgs
  unless (← isDefEq args[0]! q(ℝ)) &&
      (← isDefEq args[1]! (mkConst ``Real.instLE)) do return none
  let epsilon := args[if ge then 3 else 2]!
  let upper ← Affine.reduceStructure args[if ge then 2 else 3]!
  unless ← isDefEq upper denominator do return none
  let some positive ← positiveProof? point epsilon | return none
  return some (← mkAppM ``marginPositive #[positive, evidence])

private def denominatorPositive (point denominator : Expr)
    (retainedBodies : Array Expr) (remainderProof : Expr) : MetaM Expr := do
  if let some proof ← positiveProof? point denominator then return proof
  let parts ← conjunctionParts retainedBodies.size remainderProof
  for body in retainedBodies, proof in parts do
    if let some positive ← marginInRow? point denominator body proof then
      return positive
  throwError "quadratic-over-linear rewrite was not certified: missing positive constant margin; required an independent ε with 0 < ε and a retained constraint ε ≤ {denominator}"

-- Construct a theorem using its native operation, then compare the actual
-- operation instances before accepting definitional equality of the full bound.
private def boundProof (operation bound : Expr) (denominator? : Option (Expr × Expr)) :
    MetaM Expr := do
  let operation ← Affine.reduceStructure operation
  let suffix := denominator?.isSome
  let arguments (value : Expr) := match denominator? with
    | none => #[value, bound]
    | some (denominator, positive) => #[value, denominator, bound, positive]
  let proof ← if operation.isAppOfArity ``Norm.norm 3 then do
      if suffix then
        throwError "quadratic-over-linear requires a square or sum of squares in the numerator"
      unless ← euclidean? operation.getAppArgs[0]! do
        throwError "Euclidean norm rewrite was not certified: expected EuclideanSpace ℝ (Fin n)"
      mkAppM ``PTran.Conic.SecondOrder.norm_le_iff #[operation.getAppArgs[2]!, bound]
    else if operation.isAppOfArity ``HPow.hPow 6 then do
      let base ← Affine.reduceStructure (← squareBase operation)
      if base.isAppOfArity ``Norm.norm 3 then
        unless ← euclidean? base.getAppArgs[0]! do
          throwError "squared-norm rewrite was not certified: expected a Euclidean norm on Fin n"
        mkAppM (if suffix then ``PTran.Conic.SecondOrder.norm_sq_div_le_iff
          else ``PTran.Conic.SecondOrder.norm_sq_le_iff) (arguments base.getAppArgs[2]!)
      else
        mkAppM (if suffix then ``PTran.Conic.SecondOrder.square_div_le_iff
          else ``PTran.Conic.SecondOrder.square_le_iff) (arguments base)
    else if operation.isAppOfArity ``Finset.sum 5 then do
      let args := operation.getAppArgs
      unless (← whnf args[0]!).isAppOfArity ``Fin 1 do
        throwError "sum-of-squares rewrite was not certified: expected a sum over all of Fin n"
      let vector ← withLocalDeclD `i args[0]! fun i => do
        mkLambdaFVars #[i] (← squareBase (mkApp args[4]! i))
      mkAppM (if suffix then ``PTran.Conic.SecondOrder.sumSquares_div_le_iff
        else ``PTran.Conic.SecondOrder.sumSquares_le_iff) (arguments vector)
    else
      throwError "second-order rewrite was not certified: expected a Euclidean norm, square, or sum of squares in upper-bound polarity; found {operation}"
  let (source, _) ← sides proof
  let expected := source.getAppArgs[2]!
  let expected := if suffix then expected.getAppArgs[4]! else expected
  sameOperation operation expected (if operation.isAppOfArity ``Norm.norm 3 then 1 else 2)
  if operation.isAppOfArity ``HPow.hPow 6 then
    let base ← Affine.reduceStructure operation.getAppArgs[4]!
    if base.isAppOfArity ``Norm.norm 3 then
      sameOperation base expected.getAppArgs[4]! 1
  if operation.isAppOfArity ``Finset.sum 5 then
    withLocalDeclD `i operation.getAppArgs[0]! fun i => do
      let actual ← Affine.reduceStructure (mkApp operation.getAppArgs[4]! i)
      let expected ← Affine.reduceStructure (mkApp expected.getAppArgs[4]! i)
      sameOperation actual expected 2
  return proof

private def automaticProof (point body : Expr) (retained : Array Expr)
    (remainderProof : Expr) : MetaM Expr := do
  let body ← Affine.reduceStructure body
  let ge := body.isAppOfArity ``GE.ge 4
  unless ge || body.isAppOfArity ``LE.le 4 do
    throwError "second-order rewrite was not certified: expected an upper bound, not an equality or another context"
  let args := body.getAppArgs
  unless (← isDefEq args[0]! q(ℝ)) &&
      (← isDefEq args[1]! (mkConst ``Real.instLE)) do
    throwError "second-order rewrite was not certified: unsupported scalar or order instance"
  let operation ← Affine.reduceStructure args[if ge then 3 else 2]!
  let bound := args[if ge then 2 else 3]!
  let proof ← if operation.isAppOfArity ``HDiv.hDiv 6 then do
      let numerator := operation.getAppArgs[4]!
      let denominator ← Affine.reduceStructure operation.getAppArgs[5]!
      let positive ← denominatorPositive point denominator retained remainderProof
      let proof ← boundProof numerator bound (some (denominator, positive))
      let (source, _) ← sides proof
      sameOperation operation source.getAppArgs[2]! 2
      pure proof
    else boundProof operation bound none
  let (source, _) ← sides proof
  unless ← isDefEq source body do
    throwError "second-order rewrite was not certified: the native rule does not match the complete selected bound"
  return proof

private partial def withEvidence (point body : Expr) (action : MetaM Result) : MetaM Result := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← withEvidence point (rest.instantiate1 value) action
    withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← withEvidence point (rest.instantiate1 binding) action
      return result.replaceFVars #[binding] #[value]
  else action

private def withFiniteInstances (instances : List Expr) (action : MetaM Result) : MetaM Result := do
  match instances with
  | [] => action
  | inst :: rest =>
    withLetDecl `_secondOrderFinite (← inferType inst) inst fun binding => do
      let result ← withFiniteInstances rest action
      return result.replaceFVars #[binding] #[inst]

/-- Certify one native upper bound under exactly the supplied retained rows.
The selected predicate must not be included among `retained`. -/
def plan (source : Expr) (retained : Array Expr := #[])
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Result) :=
  Affine.withIsolatedMVars do
    try
      if ← Plan.unresolved source then throwError "unresolved metavariables in selected predicate"
      for row in retained do
        if ← Plan.unresolved row then throwError "unresolved metavariables in retained constraints"
      let domain ← Plan.predicateDomain source
      let mut instances ← Affine.sourceFiniteInstances source
      for row in retained do instances := instances ++ (← Affine.sourceFiniteInstances row)
      let result ← withFiniteInstances instances.toList do
        withLocalDeclD `point domain fun point =>
          withEvidence point (mkApp source point) do
            let bodies := retained.map (mkApp · point)
            let (row, conditionalIff) ← withLocalDeclD `retained (conjunction bodies) fun evidence => do
              let proof ← automaticProof point (mkApp source point) bodies evidence
              let (_, target) ← sides proof
              if ← Affine.depends evidence target then
                throwError "generated cone row depends on feasibility evidence"
              return (← mkLambdaFVars #[point] target, ← mkLambdaFVars #[point, evidence] proof)
            let rowPredicates := #[← instantiateMVars row]
            let certifiedRows ← Plan.certifyRows rowPredicates config
            let conditionalIff ← instantiateMVars conditionalIff
            if ← Plan.unresolved conditionalIff then
              throwError "second-order certificate contains unresolved metavariables"
            checkWithKernel conditionalIff
            return { domain, rowPredicates, certifiedRows, conditionalIff }
      return .ok result
    catch error =>
      return .error { expression := source, reason := ← addMessageContext error.toMessageData }

/-- Use the ordinary exact-lift path when the checked proof does not use the
retained rows. This keeps unconditional certificates small in long scripts;
only denominator evidence extracted from retained constraints is contextual. -/
def planReplacement (source : Expr) (retained : Array Expr := #[])
    (config : Affine.Config := {}) :
    MetaM (Except Affine.AffineError (Sum Plan.Result Result)) :=
  Affine.withIsolatedMVars do
    match ← plan source retained config with
    | .error error => return .error error
    | .ok result =>
      try
        let exact? ← withLocalDeclD `point result.domain fun point => do
          let remainder := conjunction (retained.map (mkApp · point))
          withLocalDeclD `retained remainder fun evidence => do
            let proof := (mkApp2 result.conditionalIff point evidence).headBeta
            if ← Affine.depends evidence proof then return none
            let pointwise ← mkLambdaFVars #[point] proof
            let lift ← instantiateMVars (← mkAppM ``PTran.ExactConstraintLift.ofIff
              #[result.rowPredicates[0]!, pointwise])
            let lift ← Plan.checkLift source lift
            let targetIff ← mkLambdaFVars #[point]
              (mkApp (mkConst ``Iff.rfl) (mkApp result.rowPredicates[0]! point))
            checkWithKernel targetIff
            return some ({
              lift
              auxiliary? := none
              nextDomain := result.domain
              rowPredicates := result.rowPredicates
              targetIff
              certifiedRows := result.certifiedRows
            } : Plan.Result)
        return .ok (match exact? with
          | some exact => .inl exact
          | none => .inr result)
      catch error =>
        return .error { expression := source, reason := ← addMessageContext error.toMessageData }

end PTran.Elab.Conic.SecondOrder
