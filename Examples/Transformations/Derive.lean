/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Deriving constraints

`derive label : proposition using proof` appends a consequence of the current
constraints. The first example derives a positive lower bound for a logarithm;
the second derives, rewrites, and removes a redundant absolute-value bound.
-/

namespace Examples.Transformations.Derive

open Morew
noncomputable section

def logarithmic :=
  problem (y x : ℝ)
    maximize Real.log x
    subject to
      lower : 1 ≤ y
      ordered : y ≤ x

-- The proof receives the complete decision point `(y, x)` and current feasibility.
theorem marginOfFeasible :
    ∀ point, logarithmic.feasible point → 1 ≤ point.2 := by
  intro point hp
  exact hp.1.trans hp.2

-- The derived bound supplies positivity for the logarithm rule.
reformulation logarithmicConic : logarithmic := by
  derive margin : 1 ≤ x using marginOfFeasible
  hypograph t as logarithm_bound
  conic

#printp logarithmicConic
example : GlobalEquivalence logarithmic logarithmicConic := logarithmicConic.equivalence
example : IsConic logarithmicConic := logarithmicConic.isConic

-- The same bound allows exponential coordinates; 1 ≤ exp u remains a constraint.
reformulation exponentialCoordinates : logarithmic := by
  derive margin : 1 ≤ x using marginOfFeasible
  substitute x := Real.exp u
  nlp

#printp exponentialCoordinates
example : GlobalEquivalence logarithmic exponentialCoordinates :=
  exponentialCoordinates.equivalence
example : IsSmoothNLP exponentialCoordinates := exponentialCoordinates.isSmoothNLP

def interval :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

-- Derive |x| ≤ 1 and split it into two bounds. Remove the duplicate x ≤ 1
-- automatically and prove -x ≤ 1 from the remaining lower bound.
reformulation absoluteNLP : interval := by
  derive abs_bound : |x| ≤ 1 using (by
    intro point hp
    exact abs_le.mpr hp)
  nlp at abs_bound
  remove at abs_bound_nlp_1
  remove at abs_bound_nlp_2 using (by
    intro point retained
    exact neg_le.mpr retained.1)
  nlp

#printp absoluteNLP
example (x : ℝ) : absoluteNLP.feasible x ↔ -1 ≤ x ∧ x ≤ 1 := Iff.rfl
example : GlobalEquivalence interval absoluteNLP := absoluteNLP.equivalence
example : IsSmoothNLP absoluteNLP := absoluteNLP.isSmoothNLP

end
end Examples.Transformations.Derive
