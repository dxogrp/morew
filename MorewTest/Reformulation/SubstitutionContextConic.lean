/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-! Grouped positivity across substitution and conic certification. -/

namespace MorewTest.Reformulation.SubstitutionContext

open Morew
noncomputable section

namespace GroupedExponentialPositivity

-- Root simp lemmas must still discharge positivity inside retained groups
-- while the presentation simplifier preserves actual operation instances.
def source :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      positive : 0 < x
      grouped : 0 < x ∧ x ≤ 10

reformulation target : source := by
  substitute x := Real.exp u
  conic

example : GlobalEquiv source target := target.equiv
example : IsConic target := target.isConic
example : target.conicForm.data.toProblem = target := target.conicForm.represents
example (u : ℝ) : target.feasible u ↔ (u, 1, 10) ∈ EXP := Iff.rfl

end GroupedExponentialPositivity

end
end MorewTest.Reformulation.SubstitutionContext
