/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP

/-!
# Smooth NLP reformulations

`nlp at label` performs an exact rewrite of a direct nonsmooth bound; optional
`using` selects its rule.

Bare `nlp` finishes the script by applying supported exact rewrites to direct
bounds and certifying the complete objective and constraints as a smooth NLP.
It records a concrete NLP form and certificates alongside the final problem.
-/

namespace Examples.GettingStarted.NLP

open Morew
noncomputable section

def nonlinear :=
  problem (x y t : ℝ)
    minimize (x * y - 1) ^ 2 + t
    subject to
      error : |x ^ 2 - y| ≤ t

reformulation smoothConstraints : nonlinear := by
  nlp at error using Rewrite.absEpigraph -- explicit `using` clause is optional here
  nlp

#printp smoothConstraints
example : GlobalEquivalence nonlinear smoothConstraints := smoothConstraints.equivalence
example : smoothConstraints.nlpForm.data.toProblem = smoothConstraints :=
  smoothConstraints.nlpForm.represents
example : IsSmoothNLP smoothConstraints := smoothConstraints.isSmoothNLP

def negativeMinimum :=
  problem (x : ℝ)
    minimize -min (x ^ 2) (Real.sin x)

-- An epigraph of -min f g is described by the two bounds -f ≤ t and -g ≤ t.
-- These two bounds use smooth expressions.
reformulation negativeMinimumNLP : negativeMinimum := by
  epigraph t
  nlp

#printp negativeMinimumNLP
example : GlobalEquivalence negativeMinimum negativeMinimumNLP := negativeMinimumNLP.equivalence
example : IsSmoothNLP negativeMinimumNLP := negativeMinimumNLP.isSmoothNLP

end
end Examples.GettingStarted.NLP
