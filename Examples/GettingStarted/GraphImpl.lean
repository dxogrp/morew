/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Epigraphs and hypographs

Negation exchanges epigraph and hypograph inequalities:

```math
-f(x) \leq t \iff f(x) \geq -t, \qquad
-f(x) \geq t \iff f(x) \leq -t.
```

The following problems have conic and smooth NLP reformulations. The bound
`1 ≤ x` supplies the logarithm's positive domain.
-/

namespace Examples.GettingStarted.GraphImpl

open Morew

noncomputable section

def negativeLog :=
  problem (x : ℝ)
    minimize -Real.log x
    subject to
      domain : 1 ≤ x
      budget : x ≤ 3

reformulation negativeLogConic : negativeLog := by
  epigraph t
  conic

#printp negativeLog
#printp negativeLogConic

example : GlobalEquiv negativeLog negativeLogConic := negativeLogConic.equiv
example : IsConic negativeLogConic := negativeLogConic.isConic

-- The NLP keeps the logarithm and its domain constraints.
reformulation negativeLogNLP : negativeLog := by nlp

#printp negativeLogNLP
example : GlobalEquiv negativeLog negativeLogNLP := negativeLogNLP.equiv
example : IsSmoothNLP negativeLogNLP := negativeLogNLP.isSmoothNLP

def negativeNorm :=
  problem (x : EuclideanSpace ℝ (Fin 2))
    maximize -‖x‖
    subject to balance : x 0 + x 1 = 1

reformulation negativeNormConic : negativeNorm := by
  hypograph t
  conic

#printp negativeNorm
#printp negativeNormConic

example : GlobalEquiv negativeNorm negativeNormConic := negativeNormConic.equiv
example : IsConic negativeNormConic := negativeNormConic.isConic

-- The same norm bound has a smooth polynomial representation for NLPs.
reformulation negativeNormNLP : negativeNorm := by
  hypograph t
  nlp

#printp negativeNormNLP

example : GlobalEquiv negativeNorm negativeNormNLP := negativeNormNLP.equiv
example : IsSmoothNLP negativeNormNLP := negativeNormNLP.isSmoothNLP

end
end Examples.GettingStarted.GraphImpl
