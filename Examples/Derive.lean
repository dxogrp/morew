/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Making a proved consequence available to later steps

`derive label : proposition using proof` appends a visible constraint without
changing the feasible set. The proof must show that the proposition follows
from the current problem's feasibility. It can contain reasoning beyond the
bounded evidence lookup used by substitution and conic rewriting.
-/

namespace Examples.Derive

open Morew
noncomputable section

def logarithmic :=
  problem (y x : ℝ)
    maximize Real.log x
    subject to
      lower : 1 ≤ y
      ordered : y ≤ x

-- The proof receives the complete decision point `(y, x)` and current
-- feasibility. The displayed constraint labels are not Lean hypotheses.
theorem marginOfFeasible :
    ∀ point, logarithmic.feasible point → 1 ≤ point.2 := by
  intro point hp
  exact hp.1.trans hp.2

-- Once the transitive bound is an explicit row, the logarithm rule can use
-- it to establish positivity and certify the hypograph with an EXP cone.
reformulation logarithmicConic : logarithmic := by
  derive margin : 1 ≤ x using marginOfFeasible
  hypograph t as logarithm_bound
  conic

#printp logarithmicConic
example : GlobalEquivalence logarithmic logarithmicConic := logarithmicConic.equivalence
example : IsConic logarithmicConic := logarithmicConic.isConic

-- Alternatively, the same derived margin establishes exponential coverage.
-- Its transformed row `1 ≤ Real.exp u` remains: positivity alone would be a
-- tautology after substitution, but this stronger bound restricts `u`.
reformulation exponentialCoordinates : logarithmic := by
  derive margin : 1 ≤ x using marginOfFeasible
  substitute x := Real.exp u
  nlp

#printp exponentialCoordinates
example : GlobalEquivalence logarithmic exponentialCoordinates :=
  exponentialCoordinates.equivalence
example : IsSmoothNLP exponentialCoordinates := exponentialCoordinates.isSmoothNLP

end
end Examples.Derive
