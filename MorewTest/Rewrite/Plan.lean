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

assert_not_exists Morew.Conic.Constraint Morew.Elab.Conic.RowResult Morew.Elab.NLP.Rows.Result

namespace MorewTest.Rewrite.Plan

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Rewrite.Plan

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

private def graph : Morew.GraphRepresentation (fun x : ℝ => x + 1) where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists _ _ := by simp

private def epigraph : Morew.EpigraphRepresentation (fun x : ℝ => x + 1) where
  Auxiliary := Unit
  target x y _ := x + 1 ≤ y
  source_iff_exists _ _ := by simp

private def hypograph : Morew.HypographRepresentation (fun x : ℝ => x + 1) where
  Auxiliary := Unit
  target x y _ := y ≤ x + 1
  source_iff_exists _ _ := by simp

private def identity (bound : ℝ) :
    Morew.ExactConstraintLift (fun x : ℝ => x ≤ bound ∧ x = x) :=
  .ofIff (fun x => x ≤ bound ∧ x = x) (fun _ => Iff.rfl)

private def auxiliary : Morew.ExactConstraintLift (fun x : ℝ => x ≤ 1) where
  Auxiliary := ℝ
  target x a := a = 0 ∧ x ≤ 1
  source_iff_exists _ := by simp

private def adapts (source rule : TSyntax `term) : TermElabM Unit := do
  let source ← elaborate source
  let rule ← elaborate rule
  let lift ← customLift source (← predicateDomain source) rule
  discard <| checkLift source lift

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
  expectRejected do discard <| checkLift source wrong
  let lift ← elaborate (← `(identity 2))
  let row₁ ← elaborate (← `(fun x : ℝ => x ≤ 2))
  let row₂ ← elaborate (← `(fun x : ℝ => x = x))
  let targetIff ← elaborate (← `(fun x : ℝ => (Iff.rfl : (x ≤ 2 ∧ x = x) ↔ _)))
  let result : Result := {
    lift, auxiliary? := none, nextDomain := mkConst ``Real
    rowPredicates := #[row₁, row₂], targetIff }
  result.checkTargetIff
  expectRejected ({ result with rowPredicates := #[row₂, row₁] }.checkTargetIff)
  expectRejected ({ result with rowPredicates := #[row₁] }.checkTargetIff)
  let lift ← elaborate (← `(Morew.ExactConstraintLift.ofIff
    (fun _ : ℝ => True) (fun _ => Iff.rfl)))
  let targetIff ← elaborate (← `(fun _ : ℝ => (Iff.rfl : True ↔ True)))
  ({ lift, auxiliary? := none, nextDomain := mkConst ``Real
     rowPredicates := #[], targetIff } : Result).checkTargetIff
  let lift ← elaborate (← `(auxiliary))
  let nextDomain ← mkAppM ``Prod #[mkConst ``Real, mkConst ``Real]
  let row₁ ← elaborate (← `(fun p : ℝ × ℝ => p.2 = 0))
  let row₂ ← elaborate (← `(fun p : ℝ × ℝ => p.1 ≤ 1))
  let targetIff ← elaborate (← `(fun p : ℝ × ℝ =>
    (Iff.rfl : (p.2 = 0 ∧ p.1 ≤ 1) ↔ _)))
  let result : Result := {
    lift, auxiliary? := some (mkConst ``Real), nextDomain
    rowPredicates := #[row₁, row₂], targetIff }
  result.checkTargetIff
  expectRejected ({ result with auxiliary? := none }.checkTargetIff)

-- Rebased proofs must remain closed after their temporary parameter leaves scope.
run_elab do
  let two ← elaborate (← `((2 : ℝ)))
  let result ← withLocalDeclD `bound (mkConst ``Real) fun bound => do
    let lift ← mkAppM ``identity #[bound]
    let rows ← withLocalDeclD `point (mkConst ``Real) fun point => do
      let first ← mkAppM ``LE.le #[point, bound]
      let second ← mkEq point point
      return #[← mkLambdaFVars #[point] first, ← mkLambdaFVars #[point] second]
    let targetIff ← withLocalDeclD `point (mkConst ``Real) fun point => do
      let body := Morew.Elab.Rewrite.Decomposition.conjunction
        (rows.toList.map (mkApp · point))
      mkLambdaFVars #[point] (mkApp (mkConst ``Iff.rfl) body)
    let result : Result := {
      lift, auxiliary? := none, nextDomain := mkConst ``Real
      rowPredicates := rows, targetIff }
    return result.replaceFVars #[bound] #[two]
  result.checkTargetIff
  for expression in #[result.lift, result.nextDomain, result.targetIff] ++ result.rowPredicates do
    if expression.hasFVar || expression.hasMVar then
      throwError "scoped evidence escaped the shared replacement"

end MorewTest.Rewrite.Plan
