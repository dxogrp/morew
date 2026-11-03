/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Named vector norms

`Fn.norm1`, `Fn.norm2`, and `Fn.normInf` denote the sum of absolute coordinates,
Euclidean norm, and maximum absolute coordinate, respectively. They operate on
ordinary real vectors without requiring a norm scope or a `WithLp` conversion.

This model fits a vector to given data in the one-norm, subject to a Euclidean
radius and a bound on every coordinate. Its conic and smooth NLP formulations
are both exact: the Euclidean bound becomes an SOC row for conic certification
and a nonnegative bound plus a squared inequality for NLP certification.
-/

namespace Examples.Models.Norms

open Morew

noncomputable section

def normBudget (b : Fin n → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm1 (x - b)
    subject to
      radius : Fn.norm2 x ≤ 2
      peak : Fn.normInf x ≤ 1

variable (b : Fin n → ℝ)

reformulation normConic : (normBudget b) := by
  epigraph t as residualBound
  conic at radius
  conic

#printp normConic

example : GlobalEquivalence (normBudget b) (normConic b) := normConic.equivalence b
example : (normConic.conicForm b).data.toProblem = normConic b :=
  (normConic.conicForm b).represents
example : IsConic (normConic b) := normConic.isConic b

-- The same source model can instead use the smooth polynomial representation.
reformulation normNLP : (normBudget b) := by
  epigraph t as residualBound
  nlp at radius
  nlp

#printp normNLP

example : GlobalEquivalence (normBudget b) (normNLP b) := normNLP.equivalence b
example : (normNLP.nlpForm b).data.toProblem = normNLP b :=
  (normNLP.nlpForm b).represents
example : IsSmoothNLP (normNLP b) := normNLP.isSmoothNLP b

end
end Examples.Models.Norms
