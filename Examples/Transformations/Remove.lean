/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Removing redundant constraints

`remove at label` removes a duplicate constraint or a supported tautology.
`remove at label using proof` removes a constraint implied by the remaining ones.
Here `1 ≤ x` implies the weaker bound `0 ≤ x`.
-/

namespace Examples.Transformations.Remove

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
example : GlobalEquiv bounded simplified := simplified.equiv
example : IsConic simplified := simplified.isConic

end
end Examples.Transformations.Remove
