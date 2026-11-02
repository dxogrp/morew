/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Making a proved consequence available to later steps

`derive label : proposition using proof` appends a visible constraint without
changing the feasible set. The proof must show that the proposition follows
from the current problem's feasibility.
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

-- The proof receives the complete decision point `(y, x)` and current feasibility.
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

-- The derived bound proves positivity, allowing `x := Real.exp u`.
-- After substitution, the margin becomes `1 ≤ Real.exp u`.
-- This row remains because it is not a tautology, although it is still
-- implied by the other constraints.
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

-- A derived absolute-value bound can be lowered and its redundant pieces
-- removed. The generated upper bound duplicates an existing row exactly;
-- the sign-flipped lower bound needs an explicit implication proof.
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
example : absoluteNLP.nlpForm.data.toProblem = absoluteNLP := absoluteNLP.nlpForm.represents

end
end Examples.Derive
