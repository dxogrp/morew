/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Command

/-!
# Certified smooth-NLP reformulations

`nlp at label` performs an exact rewrite of a direct nonsmooth bound; optional
`using` selects its rule. For a nested term, first expose it with an occurrence
epigraph or hypograph step.

Bare `nlp` finishes the script by applying supported exact rewrites to direct
bounds and certifying the complete objective and constraints as a smooth NLP.
It records a concrete NLP form and certificates alongside the final problem.
-/

namespace Morew.Examples.NLP

open Morew
noncomputable section

def nonlinear :=
  problem (x y t : ℝ)
    minimize (x * y - 1) ^ 2 + t
    subject to
      error : |x ^ 2 - y| ≤ t
      budget : |x| + y ^ 2 ≤ 10

reformulation smoothConstraints : nonlinear := by
  nlp at error using Rewrite.absEpigraph -- explicit `using` clause is optional here
  -- Expose the nested absolute value as the direct bound named `magnitude`.
  epigraph a at (|x|) in budget as magnitude
  nlp at magnitude
  nlp

#printp smoothConstraints
example : GlobalEquivalence nonlinear smoothConstraints := smoothConstraints.equivalence
example : smoothConstraints.nlpForm.data.toProblem = smoothConstraints :=
  smoothConstraints.nlpForm.represents
example : IsSmoothNLP smoothConstraints := smoothConstraints.isSmoothNLP

def normBound (n : ℕ) :=
  problem (v : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      norm : ‖WithLp.toLp 2 v‖ ≤ t

variable (n : ℕ)

-- Automatic rewriting yields `0 ≤ t` and `∑ i, v i ^ 2 ≤ t ^ 2`,
-- preserving the symbolic dimension `n`.
reformulation squaredNorm : (normBound n) := by
  nlp

#printp squaredNorm
example : GlobalEquivalence (normBound n) (squaredNorm n) := squaredNorm.equivalence n
example : IsSmoothNLP (squaredNorm n) := squaredNorm.isSmoothNLP n

end
end Morew.Examples.NLP
