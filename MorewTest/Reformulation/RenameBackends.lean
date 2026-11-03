/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.Rename

/-! Backend integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.Rename

open Morew
noncomputable section

-- Current labels select rewrites, and generated families use that current
-- spelling. Individual generated rows can then be renamed and selected again.
reformulation conicRows : absoluteSource := by
  rename magnitude to cap
  conic at cap
  rename cap_conic_1 to upper
  conic at upper using upperLift
  rename upper_conic_1 to upper

reformulation nlpRows : absoluteSource := by
  rename magnitude to cap
  nlp at cap
  rename cap_nlp_1 to upper
  nlp at upper using upperLift
  rename upper_nlp_1 to upper

example (x : ℝ) : conicRows.feasible x ↔
    -5 ≤ x ∧ x ≤ 3 ∧ -x ≤ 3 ∧ x ≤ 5 := Iff.rfl
example : nlpRows = conicRows := rfl
example : GlobalEquivalence absoluteSource conicRows := conicRows.equivalence
example : GlobalEquivalence absoluteSource nlpRows := nlpRows.equivalence

reformulation conicTerminal : absoluteSource := by
  rename magnitude to cap
  conic

reformulation nlpTerminal : absoluteSource := by
  rename magnitude to cap
  nlp

example : IsConic conicTerminal := conicTerminal.isConic
example : IsSmoothNLP nlpTerminal := nlpTerminal.isSmoothNLP

reformulation occurrenceRows : absoluteSource := by
  rename magnitude to budget
  epigraph a at (|x|) in budget as magnitude
  rename magnitude to lifted
  conic at lifted
  rename lifted_conic_1 to positive_side

example (x a : ℝ) : occurrenceRows.feasible (x, a) ↔
    -5 ≤ x ∧ a ≤ 3 ∧ x ≤ 5 ∧ x ≤ a ∧ -x ≤ a := Iff.rfl

reformulation vectorConic : vectorSource := by
  rename bounds to coordinate_bounds
  conic

example : IsConic vectorConic := vectorConic.isConic
example : GlobalEquivalence vectorSource vectorConic := vectorConic.equivalence

run_cmd do
  for (name, expected) in #[
      (``conicRows, #[`before, `upper, `cap_conic_2, `after]),
      (``nlpRows, #[`before, `upper, `cap_nlp_2, `after]),
      (``occurrenceRows, #[`before, `budget, `after, `positive_side, `lifted_conic_2]),
      (``vectorConic, #[`coordinate_bounds])] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing renamed presentation for {name}"
    let actual := view.constraints.map (·.name.eraseMacroScopes)
    unless actual == expected do
      Lean.throwError "unexpected labels for {name}: {actual}; expected {expected}"

end
end MorewTest.Reformulation.Rename
