/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Automatic

/-!
# Checked second-order replacements

The focused interface discovers registered second-order records and checks the
same bounded retained-domain obligations as the complete conic registry path.
-/

namespace Morew.Elab.Conic.SecondOrder

open Lean Lean.Meta

/-- A same-domain replacement using checked retained-evidence certificates. -/
abbrev Result := Plan.ContextualResult

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
    if ← Morew.Elab.Rewrite.Plan.unresolved predicate then return false
    withNewMCtxDepth do
      let domain ← Morew.Elab.Rewrite.Plan.predicateDomain predicate
      withLocalDeclD `point domain fun point => do
        let body ← Affine.reduceStructure (mkApp predicate point)
        if body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``GE.ge 4 ||
            body.isAppOfArity ``Eq 3 then
          let args := body.getAppArgs
          return (← operationCandidate args[args.size - 2]!) ||
            (← operationCandidate args.back!)
        return false
  finally saved.restore

/-- Certify a unique registered second-order replacement. -/
def planReplacement (source : Expr) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError Plan.Prepared) :=
  Automatic.planUnique source retained provider ((`Morew.Conic.SecondOrder).isPrefixOf ·)

private theorem unitExists (p : Unit → Prop) : (∃ u, p u) ↔ p () := by
  constructor
  · rintro ⟨⟨⟩, h⟩
    exact h
  · exact fun h => ⟨(), h⟩

/-- Present a second-order replacement uniformly as a same-domain certificate. -/
def plan (source : Expr) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError Result) :=
  Affine.withIsolatedMVars do
    match ← planReplacement source retained provider with
    | .error error => return .error error
    | .ok (.inr contextual) => return .ok contextual
    | .ok (.inl exact) =>
      try
        if exact.auxiliary?.isSome then throwError "second-order replacement introduced auxiliaries"
        let domain ← Morew.Elab.Rewrite.Plan.predicateDomain source
        let conditionalIff ← withLocalDeclD `point domain fun point => do
          let remainder := Morew.Elab.Rewrite.Decomposition.conjunction
            (retained.toList.map (mkApp · point))
          withLocalDeclD `retained remainder fun evidence => do
            let proof ← mkAppM ``Morew.ExactConstraintLift.source_iff_exists #[exact.lift, point]
            let target ← mkAppM ``Morew.ExactConstraintLift.target #[exact.lift, point]
            let proof ← mkAppM ``Iff.trans #[proof, ← mkAppM ``unitExists #[target]]
            let proof ← mkAppM ``Iff.trans #[proof, mkApp exact.targetIff point]
            mkLambdaFVars #[point, evidence] proof
        checkWithKernel conditionalIff
        return .ok {
          domain
          rowPredicates := exact.rowPredicates
          certifiedRows := exact.certifiedRows
          conditionalIff }
      catch error => return .error {
        expression := source, reason := ← addMessageContext error.toMessageData }

end Morew.Elab.Conic.SecondOrder
