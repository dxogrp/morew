/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Removing selected constraints with checked evidence

`remove at label` removes a whole-row duplicate or a supported tautology.
`remove at label using proof` removes a row implied by the remaining rows.
-/

namespace Examples.Remove

open Morew
noncomputable section

def bounded :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : 1 ≤ x
      duplicate : 1 ≤ x
      weaker : 0 ≤ x
      tautology : x = x

reformulation simplified : bounded := by
  remove at duplicate
  remove at tautology
  -- The proof receives the current decision point and only the retained row.
  remove at weaker using (by
    intro point retained
    exact le_trans zero_le_one retained)
  conic

#printp simplified
example (x : ℝ) : simplified.feasible x ↔ 1 ≤ x := by
  change 0 ≤ x - 1 ↔ 1 ≤ x
  exact sub_nonneg
example : GlobalEquivalence bounded simplified := simplified.equivalence
example : IsConic simplified := simplified.isConic

end
end Examples.Remove
