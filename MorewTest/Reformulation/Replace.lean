/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Shared selected-row replacement preserves both command presentations

Both paths remove an empty row, consume a qualified label, select a generated
label again, and append an auxiliary vector. Untouched rows and distinct local
definitions retain their spelling across the resulting checkpoint.
-/

namespace MorewTest.Reformulation.Replace

open Morew
open scoped ENNReal

noncomputable section

def source :=
  problem (x : ℝ) (v : Fin 1 → ℝ)
    let first := x + 1
    let second := x + 1
    minimize first + second
    subject to
      before : x < 20
      removable : x = x
      labels.cap : |x| ≤ 3
      norm : ‖WithLp.toLp 1 v‖ ≤ 5
      after : first ≤ second + 1

def removeLift : ExactConstraintLift (fun p : ℝ × (Fin 1 → ℝ) => p.1 = p.1) :=
  .ofIff (fun _ => True) (fun _ => by simp)

def upperLift : ExactConstraintLift (fun p : ℝ × (Fin 1 → ℝ) => p.1 ≤ 3) :=
  .ofIff (fun p => p.1 ≤ 3) (fun _ => Iff.rfl)

reformulation conicTarget : source := by
  conic at removable using removeLift
  conic at labels.cap
  conic at cap_conic_1 using upperLift
  conic at norm

reformulation nlpTarget : source := by
  nlp at removable using removeLift
  nlp at labels.cap
  nlp at cap_nlp_1 using upperLift
  nlp at norm

example : GlobalEquivalence source conicTarget := conicTarget.equivalence
example : GlobalEquivalence source nlpTarget := nlpTarget.equivalence

example (x : ℝ) (v u : Fin 1 → ℝ) :
    conicTarget.feasible ((x, v), u) ↔
      x < 20 ∧ x ≤ 3 ∧ -x ≤ 3 ∧ v ≤ u ∧ -v ≤ u ∧
        (∑ i, u i) ≤ 5 ∧ x + 1 ≤ (x + 1) + 1 := Iff.rfl

example (x : ℝ) (v u : Fin 1 → ℝ) :
    nlpTarget.feasible ((x, v), u) ↔ conicTarget.feasible ((x, v), u) := Iff.rfl

example (x : ℝ) (v u : Fin 1 → ℝ) :
    conicTarget.objective ((x, v), u) = (x + 1) + (x + 1) := rfl

example (x : ℝ) (v u : Fin 1 → ℝ) :
    nlpTarget.objective ((x, v), u) = (x + 1) + (x + 1) := rfl

/--
info: problem (x : ℝ) (v norm_aux : Fin 1 → ℝ)
  let first := x + 1
  let second := x + 1
  minimize first + second
  subject to
    before : x < 20
    cap_conic_1_conic_1 : x ≤ 3
    cap_conic_2 : -x ≤ 3
    norm_conic_1 : v ≤ norm_aux
    norm_conic_2 : -v ≤ norm_aux
    norm_conic_3 : ∑ i, norm_aux i ≤ 5
    after : first ≤ second + 1
-/
#guard_msgs in
#printp conicTarget

/--
info: problem (x : ℝ) (v norm_aux : Fin 1 → ℝ)
  let first := x + 1
  let second := x + 1
  minimize first + second
  subject to
    before : x < 20
    cap_nlp_1_nlp_1 : x ≤ 3
    cap_nlp_2 : -x ≤ 3
    norm_nlp_1 : v ≤ norm_aux
    norm_nlp_2 : -v ≤ norm_aux
    norm_nlp_3 : ∑ i, norm_aux i ≤ 5
    after : first ≤ second + 1
-/
#guard_msgs in
#printp nlpTarget

reformulation conicContinued : conicTarget := by
  epigraph bound at first as first_bound

reformulation nlpContinued : nlpTarget := by
  epigraph bound at first as first_bound

example : GlobalEquivalence conicTarget conicContinued := conicContinued.equivalence
example : GlobalEquivalence nlpTarget nlpContinued := nlpContinued.equivalence

end
end MorewTest.Reformulation.Replace
