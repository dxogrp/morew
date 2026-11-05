/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.OccurrenceBounds

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.OccurrenceBounds

open Morew
noncomputable section

reformulation converted : compound := by
  epigraph a at (x ^ 2)
  epigraph b at (|x|)
  conic

example : GlobalEquiv compound converted := converted.equiv
example : Conic.Form converted := converted.conicForm
example : IsConic converted := converted.isConic
example : converted.conicForm.data.rowCount = 3 := rfl

reformulation targetedConverted : compound := by
  epigraph a at (x ^ 2) as square_bound
  conic at square_bound
  epigraph b at (abs x) as magnitude_bound
  conic at magnitude_bound
  conic

example : GlobalEquiv compound targetedConverted := targetedConverted.equiv
example : IsConic targetedConverted := targetedConverted.isConic
example : targetedConverted.conicForm.data.rowCount = 3 := rfl

reformulation continued : namedSplit := by
  epigraph b at penalty
  conic

example : GlobalEquiv namedSplit continued := continued.equiv
example : IsConic continued := continued.isConic

-- The complete chain fits Lean's default heartbeat budget.
reformulation budgetedConic : budgeted := by
  epigraph a at (x ^ 2) as epi_sq_x
  epigraph b at (|x|) in budget as magnitude_bound
  epigraph c at (y ^ 2) in budget as square_bound
  epigraph d at abs_y in bound as abs_bound
  conic

example : GlobalEquiv budgeted budgetedConic := budgetedConic.equiv
example : Conic.Form budgetedConic := budgetedConic.conicForm
example : IsConic budgetedConic := budgetedConic.isConic
example : budgetedConic.conicForm.data.rowCount = 8 := rfl
example (x y a b c d : ℝ) :
    budgetedConic.objective (((((x, y), a), b), c), d) = a + y := rfl

/--
info: problem (x y a b c d : ℝ)
  let abs_y := |y|
  minimize a + y
  subject to
    budget : 10 - (b + c) ∈ ℝ₊
    bound : 5 - d ∈ ℝ₊
    epi_sq_x_conic_1 : (a, 1 / 2, ![x]) ∈ RSOC 1
    magnitude_bound_conic_1 : b - x ∈ ℝ₊
    magnitude_bound_conic_2 : b + x ∈ ℝ₊
    square_bound_conic_1 : (c, 1 / 2, ![y]) ∈ RSOC 1
    abs_bound_conic_1 : d - y ∈ ℝ₊
    abs_bound_conic_2 : d + y ∈ ℝ₊
-/
#guard_msgs in
#printp budgetedConic

reformulation maximumConverted : maximum := by
  hypograph t at score as score_bound
  conic at score_bound
  epigraph a at (abs x) in budget as magnitude_bound
  conic at magnitude_bound
  conic

example : GlobalEquiv maximum maximumConverted := maximumConverted.equiv
example : IsConic maximumConverted := maximumConverted.isConic
example : maximumConverted.conicForm.data.sense = .maximize := rfl
example : maximumConverted.conicForm.data.rowCount = 5 := rfl

end
end MorewTest.Reformulation.OccurrenceBounds
