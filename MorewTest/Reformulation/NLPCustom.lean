/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Explicit exact rules and evaluation-domain evidence for targeted NLP steps -/

namespace MorewTest.Reformulation.NLPCustom

open Morew

noncomputable section

def userSquare (x : ℝ) : ℝ := x ^ 2

def graph : GraphRepresentation userSquare where
  Auxiliary := Unit
  target x y _ := y = x ^ 2
  source_iff_exists x y := by simp [userSquare]

def epigraphRule : EpigraphRepresentation userSquare where
  Auxiliary := Unit
  target x t _ := x ^ 2 ≤ t
  source_iff_exists x t := by simp [userSquare]

def hypographRule : HypographRepresentation userSquare where
  Auxiliary := Unit
  target x t _ := t ≤ x ^ 2
  source_iff_exists x t := by simp [userSquare]

def exactRule : ExactConstraintLift
    (fun p : ℝ × ℝ => p.1 ≤ 5 ∧ p.2 ≤ 6) :=
  ExactConstraintLift.ofIff (fun p => p.1 ≤ 5 ∧ p.2 ≤ 6) (fun _ => Iff.rfl)

def source :=
  problem (x y : ℝ)
    minimize |x|
    subject to
      graph_row : y = userSquare x
      epigraph_row : userSquare x ≤ y
      hypograph_row : y ≤ userSquare x
      grouped : x ≤ 5 ∧ y ≤ 6

reformulation target : source := by
  nlp at graph_row using graph
  nlp at epigraph_row using epigraphRule
  nlp at hypograph_row using hypographRule
  nlp at grouped using exactRule

example : GlobalEquivalence source target := target.equivalence
example (x y : ℝ) : target.feasible (x, y) ↔
    y = x ^ 2 ∧ x ^ 2 ≤ y ∧ y ≤ x ^ 2 ∧ x ≤ 5 ∧ y ≤ 6 := Iff.rfl

def absoluteGraph : GraphRepresentation (fun x : ℝ => |x|) where
  Auxiliary := Unit
  target x y _ := 0 ≤ y ∧ y ^ 2 = x ^ 2
  source_iff_exists x y := by
    simp only [exists_const]
    constructor
    · intro h
      subst y
      exact ⟨abs_nonneg x, sq_abs x⟩
    · rintro ⟨hy, h⟩
      simpa only [abs_of_nonneg hy] using (sq_eq_sq_iff_abs_eq_abs y x).mp h

def absoluteGraphSource :=
  problem (x y : ℝ)
    maximize x * y
    subject to
      graph : |x| = y

reformulation absoluteGraphTarget : absoluteGraphSource := by
  nlp at graph using absoluteGraph

example : GlobalEquivalence absoluteGraphSource absoluteGraphTarget :=
  absoluteGraphTarget.equivalence

-- A generated guard may establish the domain only after unconditional exactness
-- has been checked. The target's log is smooth on the open set u > 0.
def guardedLift : ExactConstraintLift (fun x : ℝ => 0 ≤ x) where
  Auxiliary := ℝ
  target x u := u = 1 ∧ Real.log u = 0 ∧ 0 ≤ x
  source_iff_exists x := by simp

def guardedSource :=
  problem (x : ℝ)
    minimize x
    subject to
      before : x < 10
      positive : 0 ≤ x
      after : x ≤ 20

reformulation guardedTarget : guardedSource := by
  nlp at positive using guardedLift

example : GlobalEquivalence guardedSource guardedTarget := guardedTarget.equivalence
example (x u : ℝ) : guardedTarget.feasible (x, u) ↔
    x < 10 ∧ u = 1 ∧ Real.log u = 0 ∧ 0 ≤ x ∧ x ≤ 20 := Iff.rfl

def removableLift : ExactConstraintLift (fun x : ℝ => x = x) :=
  ExactConstraintLift.ofIff (fun _ => True) (fun _ => by simp)

def removableSource :=
  problem (x : ℝ)
    minimize |x|
    subject to
      removable : x = x
      bound : |x| ≤ 3

reformulation removableTarget : removableSource := by
  nlp at removable using removableLift
  nlp at bound

example (x : ℝ) : removableTarget.feasible x ↔ x ≤ 3 ∧ -x ≤ 3 := Iff.rfl

def restrictedSource :=
  problem (x t : ℝ)
    minimize |x|
    subject to
      positive : 1 ≤ x
      magnitude : |Real.log x| ≤ t

reformulation restrictedTarget : restrictedSource := by
  nlp at magnitude

example : GlobalEquivalence restrictedSource restrictedTarget := restrictedTarget.equivalence

section FiniteEvidence

variable (n : ℕ)

def familySource :=
  problem (v : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      positive : (fun _ => (1 : ℝ)) ≤ v
      magnitude : |∑ i, Real.log (v i)| ≤ t

reformulation familyTarget : (familySource n) := by
  nlp at magnitude

example : GlobalEquivalence (familySource n) (familyTarget n) := familyTarget.equivalence n

def literalSource :=
  problem (v : Fin 2 → ℝ)
    minimize v 1
    subject to
      positive : ∀ i, 1 ≤ v i
      magnitude : |Real.log (v 0)| ≤ 3

reformulation literalTarget : literalSource := by
  nlp at magnitude

example : GlobalEquivalence literalSource literalTarget := literalTarget.equivalence

end FiniteEvidence

section ParameterEvidence

variable {ι : Type} (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ)
variable (ha : ∀ i ∈ s, 0 < a i)

def supportedSource :=
  problem (x t : ℝ)
    minimize x
    subject to
      magnitude : s.sup' hs (fun i => Real.log (a i) * x ^ 2) ≤ t

reformulation supportedTarget : (supportedSource s hs a) := by
  nlp at magnitude

example : GlobalEquivalence (supportedSource s hs a) (supportedTarget s a) :=
  supportedTarget.equivalence s hs a

end ParameterEvidence

end
end MorewTest.Reformulation.NLPCustom
