/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Domain
import Morew.Elab.Conic.Symmetry
import Morew.Conic.PSD.PositiveDefinite

/-!
# Checked positive-definite matrix domains

Matrix-fraction premises come from independent hypotheses, retained positive
definiteness, a retained positive scalar margin, or a retained identity-block
PSD witness. Every consequence is a checked theorem. In particular, the
selected row and its prospective replacement never establish their own domain.
Global symmetry is certified separately when the generated rows are assembled.
-/

namespace Morew.Elab.Conic.MatrixDomain

open Lean Lean.Meta Qq
open Morew.Elab.Rewrite.Decomposition (conjunctionParts)

private def canonicalPositiveDefinite (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  P.PosDef

private def canonicalMargin (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) (epsilon : ℝ) :
    Matrix (Fin n) (Fin n) ℝ := P - epsilon • 1

private def canonicalIdentity (n : Nat) : Matrix (Fin n) (Fin n) ℝ := 1

private theorem positiveDefiniteOfMargin {n : Nat} (P : Matrix (Fin n) (Fin n) ℝ)
    (epsilon : ℝ) (positive : 0 < epsilon) (bound : (P - epsilon • 1).PosSemidef) :
    P.PosDef := by
  have identity : (epsilon • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    Matrix.PosDef.one.smul positive
  simpa only [add_sub_cancel] using identity.add_posSemidef bound

private def samePrefix (actual expected : Expr) (operands : Nat) : MetaM Bool := do
  unless actual.getAppFn == expected.getAppFn &&
      actual.getAppNumArgs == expected.getAppNumArgs do return false
  let actualArgs := actual.getAppArgs
  let expectedArgs := expected.getAppArgs
  for i in [:actualArgs.size - operands] do
    unless ← isDefEq actualArgs[i]! expectedArgs[i]! do return false
  return true

private def squareDimension? (point matrix : Expr) : MetaM (Option Expr) := do
  let .forallE _ row columnType _ ← whnf (← inferType matrix) | return none
  let .forallE _ column scalar _ ← whnf columnType | return none
  let row ← whnf row
  let column ← whnf column
  unless row.isAppOfArity ``Fin 1 && column.isAppOfArity ``Fin 1 &&
      (← isDefEq row column) && (← whnf scalar).isConstOf ``Real do return none
  let n := row.getAppArgs[0]!
  if (← Expr.depends point n) || (← Expr.hasUnresolved n) then return none
  return some n

private def positiveDefiniteGoal (n matrix : Expr) : MetaM Expr := do
  return (mkAppN (← getConstInfo ``canonicalPositiveDefinite).value! #[n, matrix]).headBeta

private partial def directEvidence? (goal body proof : Expr) (universal := false)
    (fuel := 32) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let body ← Expr.reduceStructure body
  if universal then
    if let .forallE _ domain rest _ := body then
      let argument ← mkFreshExprMVar domain
      return ← directEvidence? goal (rest.instantiate1 argument) (mkApp proof argument)
        true (fuel - 1)
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    let saved ← saveState
    if let some result ← directEvidence? goal args[0]! (← mkAppM ``And.left #[proof])
        universal (fuel - 1) then
      return some result
    saved.restore
    return ← directEvidence? goal args[1]! (← mkAppM ``And.right #[proof])
      universal (fuel - 1)
  unless body.isAppOf ``Matrix.PosDef && (← samePrefix body goal 1) &&
      (← isDefEq body goal) do return none
  let proof ← instantiateMVars proof
  if ← Expr.hasUnresolved proof then return none
  return some proof

private def independentEvidence? (point goal : Expr) : MetaM (Option Expr) := do
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let proof := declaration.toExpr
    unless ← isProp declaration.type do continue
    if (← Expr.depends point proof) || (← Expr.hasUnresolved proof) ||
        (← Evidence.hasPlaceholders proof) then continue
    let saved ← saveState
    if let some result ← directEvidence? goal declaration.type proof true then
      let result ← instantiateMVars result
      unless ← Expr.hasUnresolved result do return some result
    saved.restore
  return none

private theorem positiveDefiniteOfTransposedIdentity {n : Nat}
    (P W : Matrix (Fin n) (Fin n) ℝ)
    (h : (Morew.Conic.fromBlocksFin P 1 (1 : Matrix (Fin n) (Fin n) ℝ).transpose W).PosSemidef) :
    P.PosDef := by
  apply Morew.Conic.posDef_of_fromBlocksFin_identity_posSemidef P W
  simpa only [Matrix.transpose_one] using h

-- Expose only canonical bundled constructors and arithmetic. Checking the
-- operation prefix before reducing it prevents a custom subtraction or scalar
-- action from masquerading as a positive margin at particular operands.
private partial def bundledCoordinate? (value : Expr) (fuel := 32) : MetaM (Option Expr) := do
  if fuel == 0 then return none
  let value ← Expr.reduceStructure value
  if value.isAppOfArity ``Morew.Conic.SymmetricMatrix.ofMatrix 3 then
    return some value.getAppArgs[1]!
  if value.isAppOfArity ``Morew.Conic.SymmetricMatrix.fromBlocks 5 then
    let args := value.getAppArgs
    let equality ← inferType (← mkAppM ``Morew.Conic.SymmetricMatrix.toMatrix_fromBlocks
      #[args[2]!, args[3]!, args[4]!])
    return some equality.getAppArgs[2]!
  let rule? := if value.isAppOfArity ``HSub.hSub 6 then
      some ``Morew.Conic.SymmetricMatrix.toMatrix_sub
    else if value.isAppOfArity ``HSMul.hSMul 6 then
      some ``Morew.Conic.SymmetricMatrix.toMatrix_smul
    else none
  if let some rule := rule? then
    let args := value.getAppArgs
    let type ← inferType value
    unless ← isDefEq (← inferType args[5]!) type do return none
    let leftType := if rule == ``Morew.Conic.SymmetricMatrix.toMatrix_sub then type else q(ℝ)
    unless ← isDefEq (← inferType args[4]!) leftType do return none
    let equality ← inferType (← mkAppM rule #[args[4]!, args[5]!])
    let canonical := equality.getAppArgs[1]!.getAppArgs[1]!
    unless ← samePrefix value canonical 2 do return none
    let some right ← bundledCoordinate? args[5]! (fuel - 1) | return none
    let left ← if rule == ``Morew.Conic.SymmetricMatrix.toMatrix_sub then
        bundledCoordinate? args[4]! (fuel - 1)
      else pure (some args[4]!)
    let some left := left | return none
    let result := equality.getAppArgs[2]!
    return some (mkAppN result.getAppFn ((result.getAppArgs.set! 4 left).set! 5 right))
  return some (← mkAppM ``Morew.Conic.SymmetricMatrix.toMatrix #[value])

private def fromSemidefinite? (point n matrix body proof : Expr) : MetaM (Option Expr) := do
  let some coordinate ← positiveSemidefiniteValue? point body | return none
  let coordinate ← if coordinate.isAppOfArity ``Morew.Conic.SymmetricMatrix.toMatrix 2 then
      bundledCoordinate? coordinate.getAppArgs[1]!
    else pure (some coordinate)
  let some coordinate := coordinate | return none
  let coordinate ← Expr.reduceStructure coordinate
  if coordinate.isAppOfArity ``Morew.Conic.fromBlocksFin 6 then
    let args := coordinate.getAppArgs
    unless (← isDefEq args[0]! n) && (← isDefEq args[1]! n) &&
        (← isDefEq args[2]! matrix) do return none
    let identity := (mkApp (← getConstInfo ``canonicalIdentity).value! n).headBeta
    unless ← isDefEq args[3]! identity do return none
    if ← isDefEq args[4]! identity then
      return some (← mkAppM ``Morew.Conic.posDef_of_fromBlocksFin_identity_posSemidef
        #[matrix, args[5]!, proof])
    unless ← isDefEq args[4]! (← mkAppM ``Matrix.transpose #[identity]) do return none
    return some (← mkAppM ``positiveDefiniteOfTransposedIdentity #[matrix, args[5]!, proof])
  unless coordinate.isAppOfArity ``HSub.hSub 6 do return none
  let args := coordinate.getAppArgs
  unless ← isDefEq args[4]! matrix do return none
  let lower ← Expr.reduceStructure args[5]!
  unless lower.isAppOfArity ``HSMul.hSMul 6 do return none
  let epsilon := lower.getAppArgs[4]!
  unless ← isDefEq (← inferType epsilon) q(ℝ) do return none
  let canonical := (mkAppN (← getConstInfo ``canonicalMargin).value!
    #[n, matrix, epsilon]).headBeta
  unless (← samePrefix coordinate canonical 2) &&
      (← samePrefix lower canonical.getAppArgs[5]! 2) &&
      (← isDefEq coordinate canonical) do return none
  let some positive ← Domain.constantSign? point epsilon true | return none
  return some (← mkAppM ``positiveDefiniteOfMargin #[matrix, epsilon, positive, proof])

private partial def retainedEvidence? (point n matrix goal body proof : Expr) :
    MetaM (Option Expr) := do
  let body ← Expr.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Expr.depends point type) || (← Expr.depends point value) then
      return ← retainedEvidence? point n matrix goal (rest.instantiate1 value) proof
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← retainedEvidence? point n matrix goal (rest.instantiate1 binding) proof
      result.mapM fun result => result.replaceFVarsM #[binding] #[value]
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    if let some result ← retainedEvidence? point n matrix goal args[0]!
        (← mkAppM ``And.left #[proof]) then return some result
    return ← retainedEvidence? point n matrix goal args[1]! (← mkAppM ``And.right #[proof])
  if let some result ← directEvidence? goal body proof then return some result
  return ← fromSemidefinite? point n matrix body proof

/-- Establish a canonical positive-definite premise from bounded independent
or retained evidence. The caller supplies only constraints other than the
selected row. Recognition cannot assign caller metavariables. -/
def prove? (point goal : Expr) (retained : Array Expr) (remainderProof : Expr) :
    MetaM (Option Expr) := do
  let result : Except Unit Expr ← State.withIsolatedMVars do
    if (← Expr.hasUnresolved goal) || (← Evidence.hasPlaceholders goal) then return .error ()
    unless goal.isAppOf ``Matrix.PosDef do return .error ()
    let matrix := goal.getAppArgs.back!
    let some n ← squareDimension? point matrix | return .error ()
    let canonical ← positiveDefiniteGoal n matrix
    unless (← samePrefix goal canonical 1) && (← isDefEq goal canonical) do return .error ()
    let mut result ← independentEvidence? point canonical
    if result.isNone then
      let proofs ← conjunctionParts retained.size remainderProof
      for body in retained, proof in proofs do
        if (← Expr.hasUnresolved body) || (← Evidence.hasPlaceholders body) ||
            (← Evidence.hasPlaceholders proof) then continue
        if let some evidence ← retainedEvidence? point n matrix canonical body proof then
          result := some evidence
          break
    let some proof := result | return .error ()
    if (← Expr.hasUnresolved proof) || (← Evidence.hasPlaceholders proof) then return .error ()
    unless ← isDefEq (← inferType proof) goal do return .error ()
    checkWithKernel proof
    return .ok proof
  return result.toOption

end Morew.Elab.Conic.MatrixDomain
