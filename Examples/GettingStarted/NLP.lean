/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP

/-!
# Smooth NLP reformulations

`nlp at label` rewrites a direct nonsmooth bound; `using` selects a rule explicitly.
Bare `nlp` applies supported rewrites and certifies a smooth NLP, recording its
form and equivalence certificate.

The first problem has scalar variables x, y, and t:

```math
\begin{array}{ll}
\text{minimize} & (xy-1)^2+t \\
\text{subject to} & |x^2-y| \leq t.
\end{array}
```
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

-- The bound -min(f, g) ≤ t becomes -f ≤ t and -g ≤ t, both smooth here.
reformulation negativeMinimumNLP : negativeMinimum := by
  epigraph t
  nlp

#printp negativeMinimumNLP
example : GlobalEquivalence negativeMinimum negativeMinimumNLP := negativeMinimumNLP.equivalence
example : IsSmoothNLP negativeMinimumNLP := negativeMinimumNLP.isSmoothNLP

end
end Examples.GettingStarted.NLP
