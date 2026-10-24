/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import Mathlib.Data.Real.Basic

/-!
# Exact ordered constraint rewrites

These tests check the target problem and the full equivalence type, including
the order instance for maximization, without relying on surface planning.
-/

namespace MorewTest.Conic.Rewrite

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew Morew.Elab.Reformulation

noncomputable section

def trueLift : ExactConstraintLift (fun _ : ℝ => True) :=
  ExactConstraintLift.ofIff (fun _ => True) (fun _ => Iff.rfl)

def falseLift : ExactConstraintLift (fun _ : ℝ => False) :=
  ExactConstraintLift.ofIff (fun _ => False) (fun _ => Iff.rfl)

def symmetryLift : ExactConstraintLift (fun x : ℝ => x = 0) :=
  ExactConstraintLift.ofIff (fun x => 0 = x) (fun _ => eq_comm)

def pairLift : ExactConstraintLift (fun x : ℝ => x ≤ 2 ∧ -x ≤ 2) :=
  ExactConstraintLift.ofIff (fun x => x ≤ 2 ∧ -x ≤ 2) (fun _ => Iff.rfl)

def witnessLift : ExactConstraintLift (fun x : ℝ => x ≤ 2) where
  Auxiliary := ℝ
  target x a := a = x ∧ a ≤ 2
  source_iff_exists x := by
    constructor
    · intro h
      exact ⟨x, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

def unusedAuxiliaryLift : ExactConstraintLift (fun _ : ℝ => True) where
  Auxiliary := ℝ
  target _ _ := True
  source_iff_exists _ := ⟨fun _ => ⟨0, trivial⟩, fun _ => trivial⟩

private def checkedTerm (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

private def checkRewrite (oldRows : Array (TSyntax `term)) (index : Nat)
    (liftSyntax : TSyntax `term) (auxiliarySyntax? : Option (TSyntax `term))
    (newRows : Array (TSyntax `term)) (targetIffSyntax expectedSyntax : TSyntax `term)
    (sense : ObjectiveSense := .minimize) : TermElabM Unit := do
  let domain := Lean.mkConst ``Real
  let valueType ← if sense == .maximize then mkAppM ``OrderDual #[domain] else pure domain
  let rawObjective ← checkedTerm (← `(fun x : ℝ => x))
  let objectiveType ← mkArrow domain valueType
  -- Retain the explicit dual type through inference; the expected certificate
  -- below independently checks its order instance rather than mere type aliases.
  let objective ← mkAppOptM ``id #[some objectiveType, some rawObjective]
  let predicates ← oldRows.mapM checkedTerm
  let presentation : PresentationState := {
    sense
    domainType := domain
    valueType
    binders := #[{ name := `x, type := domain }]
    objective
    constraints := predicates.mapIdx fun i predicate => {
      name := Name.mkSimple s!"row_{i}"
      predicate
    }
  }
  let auxiliary? ← auxiliarySyntax?.mapM checkedTerm
  let nextDomain ← match auxiliary? with
    | none => pure domain
    | some auxiliary => mkAppM ``Prod #[domain, auxiliary]
  let lift ← checkedTerm liftSyntax
  let rows ← newRows.mapM checkedTerm
  let targetIff ← checkedTerm targetIffSyntax
  let result ← Morew.Elab.Conic.rewriteConstraint presentation index lift auxiliary?
    nextDomain rows targetIff
  let expected ← checkedTerm expectedSyntax
  unless ← isDefEq result.targetProblem expected do
    throwError "rewrite produced the wrong target problem"
  let source ← presentation.canonicalProblem
  let order ← synthInstance (← mkAppM ``Preorder #[valueType])
  let expectedType ← mkAppOptM ``GlobalEquivalence
    #[some domain, some nextDomain, some valueType, some order, some source, some expected]
  unless ← isDefEq (← inferType result.equivalence) expectedType do
    throwError "rewrite equivalence has the wrong endpoints or optimization order"
  checkWithKernel result.targetProblem
  checkWithKernel result.equivalence

run_cmd Lean.Elab.Command.liftTermElabM do
  -- Removing the only row must result in True, with no Unit decision binder.
  checkRewrite #[← `(fun _ : ℝ => True)] 0 (← `(trueLift)) none #[]
    (← `(fun _ : ℝ => (Iff.rfl : True ↔ True)))
    (← `(Problem.mk (fun x : ℝ => x) (fun _ => True)))
  -- A custom Unit target may also retain a literal True or False row.
  checkRewrite #[← `(fun _ : ℝ => True)] 0 (← `(trueLift)) none
    #[← `(fun _ : ℝ => True)]
    (← `(fun _ : ℝ => (Iff.rfl : True ↔ True)))
    (← `(Problem.mk (fun x : ℝ => x) (fun _ => True)))
  checkRewrite #[← `(fun _ : ℝ => False)] 0 (← `(falseLift)) none
    #[← `(fun _ : ℝ => False)]
    (← `(fun _ : ℝ => (Iff.rfl : False ↔ False)))
    (← `(Problem.mk (fun x : ℝ => x) (fun _ => False)))

run_cmd Lean.Elab.Command.liftTermElabM do
  let first ← `(fun x : ℝ => x ≤ 3 ∧ 0 ≤ x)
  let last ← `(fun x : ℝ => x ≤ 7)
  checkRewrite #[first, ← `(fun _ : ℝ => True), last] 1 (← `(trueLift)) none #[]
    (← `(fun _ : ℝ => (Iff.rfl : True ↔ True)))
    (← `(Problem.mk (fun x : ℝ => x) (fun x => (x ≤ 3 ∧ 0 ≤ x) ∧ x ≤ 7)))
  checkRewrite #[first, ← `(fun x : ℝ => x = 0), last] 1
    (← `(symmetryLift)) none #[← `(fun x : ℝ => 0 = x)]
    (← `(fun x : ℝ => (Iff.rfl : 0 = x ↔ 0 = x)))
    (← `(Problem.mk (fun x : ℝ => x)
      (fun x => (x ≤ 3 ∧ 0 ≤ x) ∧ 0 = x ∧ x ≤ 7)))
  checkRewrite #[first, ← `(fun x : ℝ => x ≤ 2 ∧ -x ≤ 2), last] 1
    (← `(pairLift)) none #[← `(fun x : ℝ => x ≤ 2), ← `(fun x : ℝ => -x ≤ 2)]
    (← `(fun x : ℝ => (Iff.rfl : (x ≤ 2 ∧ -x ≤ 2) ↔ (x ≤ 2 ∧ -x ≤ 2))))
    (← `(Problem.mk (fun x : ℝ => x)
      (fun x => (x ≤ 3 ∧ 0 ≤ x) ∧ x ≤ 2 ∧ -x ≤ 2 ∧ x ≤ 7)))

run_cmd Lean.Elab.Command.liftTermElabM do
  for sense in #[ObjectiveSense.minimize, ObjectiveSense.maximize] do
    let first ← `(fun x : ℝ => x ≤ 3 ∧ 0 ≤ x)
    let last ← `(fun x : ℝ => x ≤ 7)
    checkRewrite #[first, ← `(fun x : ℝ => x ≤ 2), last] 1
      (← `(witnessLift)) (some (← `(ℝ)))
      #[← `(fun p : ℝ × ℝ => p.2 = p.1), ← `(fun p : ℝ × ℝ => p.2 ≤ 2)]
      (← `(fun p : ℝ × ℝ =>
        (Iff.rfl : (p.2 = p.1 ∧ p.2 ≤ 2) ↔ (p.2 = p.1 ∧ p.2 ≤ 2))))
      (← `(Problem.mk (fun p : ℝ × ℝ => p.1)
        (fun p => (p.1 ≤ 3 ∧ 0 ≤ p.1) ∧ p.2 = p.1 ∧ p.2 ≤ 2 ∧ p.1 ≤ 7))) sense
    checkRewrite #[← `(fun x : ℝ => x = 0)] 0
      (← `(symmetryLift)) none #[← `(fun x : ℝ => 0 = x)]
      (← `(fun x : ℝ => (Iff.rfl : 0 = x ↔ 0 = x)))
      (← `(Problem.mk (fun x : ℝ => x) (fun x => 0 = x))) sense
  checkRewrite #[← `(fun _ : ℝ => True)] 0
    (← `(unusedAuxiliaryLift)) (some (← `(ℝ))) #[]
    (← `(fun _ : ℝ × ℝ => (Iff.rfl : True ↔ True)))
    (← `(Problem.mk (fun p : ℝ × ℝ => p.1) (fun _ => True)))

end

end MorewTest.Conic.Rewrite
