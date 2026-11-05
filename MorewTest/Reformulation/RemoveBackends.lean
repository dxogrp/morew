/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.Remove

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.Remove

open Morew
noncomputable section

def absolute :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1
      magnitude : |x| ≤ 1

reformulation nlpRemoved : absolute := by
  nlp at magnitude
  remove at magnitude_nlp_1
  remove at magnitude_nlp_2 using (by intro point hp; exact neg_le.mpr hp.1)
  nlp

reformulation conicRemoved : absolute := by
  conic at magnitude
  remove at magnitude_conic_1
  remove at magnitude_conic_2 using (by intro point hp; exact neg_le.mpr hp.1)
  conic

example : IsSmoothNLP nlpRemoved := nlpRemoved.isSmoothNLP
example : IsConic conicRemoved := conicRemoved.isConic
example : GlobalEquiv absolute nlpRemoved := nlpRemoved.equiv
example : GlobalEquiv absolute conicRemoved := conicRemoved.equiv
example : nlpRemoved.nlpForm.data.toProblem = nlpRemoved := nlpRemoved.nlpForm.represents
example : conicRemoved.conicForm.data.toProblem = conicRemoved := conicRemoved.conicForm.represents

def occurrenceSource :=
  problem (x : ℝ)
    minimize x
    subject to
      tag : True
      magnitude : |x| ≤ 1

reformulation afterOccurrence : occurrenceSource := by
  epigraph a at (|x|) in magnitude as bound
  remove at tag
  derive repeated : a ≤ 1 using (by intro point hp; exact hp.1)
  remove at repeated
  conic at bound

example (x a : ℝ) : afterOccurrence.feasible (x, a) ↔
    a ≤ 1 ∧ x ≤ a ∧ -x ≤ a := Iff.rfl

def vectorSource :=
  problem (v : Fin 2 → ℝ)
    minimize ∑ i, v i
    subject to
      bounds : 0 ≤ v
      copied : 0 ≤ v

reformulation vectorRemoved : vectorSource := by
  remove at bounds
  conic

example : IsConic vectorRemoved := vectorRemoved.isConic

run_cmd do
  for (name, expected) in #[
      (``afterOccurrence, #[`magnitude, `bound_conic_1, `bound_conic_2])] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing removal presentation for {name}"
    let actual := view.constraints.map (·.name.eraseMacroScopes)
    unless actual == expected do
      Lean.throwError "unexpected labels after removal for {name}: {actual}; expected {expected}"

end
end MorewTest.Reformulation.Remove
