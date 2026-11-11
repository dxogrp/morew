/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Rewrite.Plan

/-!
# Target-independent exact planning checks

The shared planner adapts the four semantic record types and validates the exact
ordered target without importing conic recognition or smooth certification.
-/

assert_not_exists Morew.Conic.Constraint Morew.Elab.Cone.RowResult Morew.Elab.NLP.Rows.Result

namespace MorewTest.Rewrite.Plan

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Rewrite.Plan

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

private def graph : Morew.GraphRepr (fun x : ℝ => x + 1) where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists _ _ := by simp

private def epigraph : Morew.EpigraphRepr (fun x : ℝ => x + 1) where
  Auxiliary := Unit
  target x y _ := x + 1 ≤ y
  source_iff_exists _ _ := by simp

private def hypograph : Morew.HypographRepr (fun x : ℝ => x + 1) where
  Auxiliary := Unit
  target x y _ := y ≤ x + 1
  source_iff_exists _ _ := by simp

private def identity (bound : ℝ) :
    Morew.ConstraintRepr (fun x : ℝ => x ≤ bound ∧ x = x) :=
  .ofIff (fun x => x ≤ bound ∧ x = x) (fun _ => Iff.rfl)

private def auxiliary : Morew.ConstraintRepr (fun x : ℝ => x ≤ 1) where
  Auxiliary := ℝ
  target x a := a = 0 ∧ x ≤ 1
  source_iff_exists _ := by simp

private def adapts (source rule : TSyntax `term) : TermElabM Unit := do
  let source ← elaborate source
  let rule ← elaborate rule
  let repr ← customRepr source (← predicateDomain source) rule
  discard <| checkRepr source repr

run_elab do
  adapts (← `(fun x : ℝ => x ≤ 2 ∧ x = x)) (← `(identity 2))
  adapts (← `(fun p : ℝ × ℝ => p.2 = p.1 + 1)) (← `(graph))
  adapts (← `(fun p : ℝ × ℝ => p.1 + 1 = p.2)) (← `(graph))
  adapts (← `(fun p : ℝ × ℝ => p.1 + 1 ≤ p.2)) (← `(epigraph))
  adapts (← `(fun p : ℝ × ℝ => p.2 ≤ p.1 + 1)) (← `(hypograph))

private def expectRejected (action : MetaM Unit) : MetaM Unit := do
  let rejected ← try action; pure false catch _ => pure true
  unless rejected do throwError "an incorrect exact replacement passed validation"

run_elab do
  let source ← elaborate (← `(fun x : ℝ => x ≤ 1))
  let wrong ← elaborate (← `(identity 2))
  expectRejected do discard <| checkRepr source wrong
  let repr ← elaborate (← `(identity 2))
  let row₁ ← elaborate (← `(fun x : ℝ => x ≤ 2))
  let row₂ ← elaborate (← `(fun x : ℝ => x = x))
  let targetIff ← elaborate (← `(fun x : ℝ => (Iff.rfl : (x ≤ 2 ∧ x = x) ↔ _)))
  let result : Result := {
    certificate := .exact repr, auxiliary? := none, nextDomain := mkConst ``Real
    rowPredicates := #[row₁, row₂], targetIff }
  result.checkTargetIff
  expectRejected ({ result with rowPredicates := #[row₂, row₁] }.checkTargetIff)
  expectRejected ({ result with rowPredicates := #[row₁] }.checkTargetIff)
  let repr ← elaborate (← `(Morew.ConstraintRepr.ofIff
    (fun _ : ℝ => True) (fun _ => Iff.rfl)))
  let targetIff ← elaborate (← `(fun _ : ℝ => (Iff.rfl : True ↔ True)))
  ({ certificate := .exact repr, auxiliary? := none, nextDomain := mkConst ``Real
     rowPredicates := #[], targetIff } : Result).checkTargetIff
  let repr ← elaborate (← `(auxiliary))
  let nextDomain ← mkAppM ``Prod #[mkConst ``Real, mkConst ``Real]
  let row₁ ← elaborate (← `(fun p : ℝ × ℝ => p.2 = 0))
  let row₂ ← elaborate (← `(fun p : ℝ × ℝ => p.1 ≤ 1))
  let targetIff ← elaborate (← `(fun p : ℝ × ℝ =>
    (Iff.rfl : (p.2 = 0 ∧ p.1 ≤ 1) ↔ _)))
  let result : Result := {
    certificate := .exact repr, auxiliary? := some (mkConst ``Real), nextDomain
    rowPredicates := #[row₁, row₂], targetIff }
  result.checkTargetIff
  expectRejected ({ result with auxiliary? := none }.checkTargetIff)

-- Rebased proofs must remain closed after their temporary parameter leaves scope.
run_elab do
  let two ← elaborate (← `((2 : ℝ)))
  let result ← withLocalDeclD `bound (mkConst ``Real) fun bound => do
    let repr ← mkAppM ``identity #[bound]
    let rows ← withLocalDeclD `point (mkConst ``Real) fun point => do
      let first ← mkAppM ``LE.le #[point, bound]
      let second ← mkEq point point
      return #[← mkLambdaFVars #[point] first, ← mkLambdaFVars #[point] second]
    let targetIff ← withLocalDeclD `point (mkConst ``Real) fun point => do
      let body := mkAndN (rows.toList.map (mkApp · point))
      mkLambdaFVars #[point] (mkApp (mkConst ``Iff.rfl) body)
    let result : Result := {
      certificate := .exact repr, auxiliary? := none, nextDomain := mkConst ``Real
      rowPredicates := rows, targetIff }
    return result.replaceFVars #[bound] #[two]
  result.checkTargetIff
  for expression in #[result.certificate.expression, result.nextDomain, result.targetIff] ++
      result.rowPredicates do
    if expression.hasFVar || expression.hasMVar then
      throwError "scoped evidence escaped the shared replacement"

private theorem conditionalExact (x : ℝ) (retained : x = 0) :
    x ≤ 1 ↔ ∃ a : ℝ, a = x :=
  ⟨fun _ => ⟨x, rfl⟩, fun _ => retained.le.trans zero_le_one⟩

run_elab do
  let domain := Lean.mkConst ``Real
  let source ← elaborate (← `(fun x : ℝ => x ≤ 1))
  let retained ← elaborate (← `(fun x : ℝ => x = 0))
  let target ← elaborate (← `(fun x a : ℝ => a = x))
  let proof ← elaborate (← `(conditionalExact))
  let certificate : Certificate := .contextual domain target proof
  certificate.check source #[retained]
  expectRejected (certificate.check source #[])
  expectRejected (certificate.check source #[source])
  let nextDomain ← mkAppM ``Prod #[domain, domain]
  let row ← elaborate (← `(fun p : ℝ × ℝ => p.2 = p.1))
  let targetIff ← elaborate (← `(fun p : ℝ × ℝ => (Iff.rfl : p.2 = p.1 ↔ _)))
  let result : Result := {
    certificate, auxiliary? := some domain, nextDomain
    rowPredicates := #[row], targetIff }
  result.check source #[retained]
  expectRejected ({ result with auxiliary? := none }.checkTargetIff)
  expectRejected ({ result with auxiliary? := some (mkConst ``Bool) }.checkTargetIff)
  expectRejected ({ result with nextDomain := domain }.checkTargetIff)
  let closed ← withLocalDeclD `point domain fun point => do
    withLocalDeclD `retained (mkApp retained point) fun evidence => do
      let pointwise := mkApp2 proof point evidence
      let closed ← closeCertificate source point evidence domain (mkApp target point) pointwise
      match closed with
      | .contextual .. => pure ()
      | .exact _ => throwError "retained-dependent exactness lost its context"
      -- Auxiliary families may not depend on original coordinates.
      withLocalDeclD `family (← mkArrow domain (mkSort (.succ .zero))) fun family => do
        expectRejected do
          discard <| closeCertificate source point evidence (mkApp family point)
            (mkApp target point) pointwise
      -- Proof-dependent targets remain forbidden even when hidden in a local let.
      let dependentType ← mkArrow (← inferType evidence) (← mkArrow domain (mkSort .zero))
      withLocalDeclD `dependentTarget dependentType fun dependent => do
        let value := mkApp dependent evidence
        withLetDecl `alias (← inferType value) value fun binding => do
          expectRejected do
            discard <| closeCertificate source point evidence domain binding pointwise
      return closed
  closed.check source #[retained]
  for expression in #[← closed.auxiliaryType, ← closed.targetFunction, closed.expression] do
    if expression.hasFVar || expression.hasMVar then
      throwError "temporary conditional evidence escaped certificate closure"
  -- These ignored arguments reduce away, so the otherwise valid certificates
  -- are rejected specifically for placeholders hidden in local values/types.
  for synthetic in [false, true] do
    let placeholder ← mkSorry (mkConst ``Nat) synthetic
    withLetDecl `targetAlias (mkConst ``Nat) placeholder fun binding => do
      let targetBuilder ← elaborate (← `(fun (_ : ℕ) (x a : ℝ) => a = x))
      expectRejected ((Certificate.contextual domain (mkApp targetBuilder binding) proof).check
        source #[retained])
      let auxiliaryBuilder ← elaborate (← `(fun _ : ℕ => ℝ))
      expectRejected ((Certificate.contextual (mkApp auxiliaryBuilder binding) target proof).check
        source #[retained])
      let proofBuilder ← elaborate (← `(fun _ : ℕ => conditionalExact))
      expectRejected ((Certificate.contextual domain target (mkApp proofBuilder binding)).check
        source #[retained])
      let sourceBuilder ← elaborate (← `(fun (_ : ℕ) (x : ℝ) => x ≤ 1))
      expectRejected (certificate.check (mkApp sourceBuilder binding) #[retained])
    let placeholder ← mkSorry domain synthetic
    let typeBuilder ← elaborate (← `(fun _ : ℝ => ℝ))
    withLocalDeclD `bound (mkApp typeBuilder placeholder) fun bound => do
      let retainedBuilder ← elaborate (← `(fun (_ : ℝ) (x : ℝ) => x = 0))
      expectRejected (certificate.check source #[mkApp retainedBuilder bound])

run_elab do
  let source ← elaborate (← `(fun x : ℝ => x ≤ 1))
  let repr ← elaborate (← `(auxiliary))
  let target ← mkAppM ``Morew.ConstraintRepr.target #[repr]
  let proof ← mkAppM ``Morew.ConstraintRepr.source_iff_exists #[repr]
  let certificate ← withLocalDeclD `point (mkConst ``Real) fun point => do
    withLocalDeclD `retained (mkConst ``True) fun evidence => do
      closeCertificate source point evidence (mkConst ``Real)
        (mkApp target point) (mkApp proof point)
  match certificate with
  | .exact _ => pure ()
  | .contextual .. => throwError "independent exactness was unnecessarily made conditional"
  certificate.check source #[]

end MorewTest.Rewrite.Plan
