/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Epigraphs and hypographs

Negation exchanges epigraph and hypograph inequalities: `-f x ≤ t` means
`-t ≤ f x`, and `t ≤ -f x` means `f x ≤ -t`. The same identities produce
conic and smooth NLP reformulations of the two problems below.

The bound `1 ≤ x` proves positivity for both the logarithm's exponential-cone
representation and its smooth NLP certificate. The norm representation holds
on the whole Euclidean space.
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

example : GlobalEquivalence negativeLog negativeLogConic := negativeLogConic.equivalence
example : IsConic negativeLogConic := negativeLogConic.isConic

-- The NLP keeps the logarithm and its domain constraints.
reformulation negativeLogNLP : negativeLog := by nlp

#printp negativeLogNLP
example : GlobalEquivalence negativeLog negativeLogNLP := negativeLogNLP.equivalence
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

example : GlobalEquivalence negativeNorm negativeNormConic := negativeNormConic.equivalence
example : IsConic negativeNormConic := negativeNormConic.isConic

-- The same norm bound has a smooth polynomial representation for NLPs.
reformulation negativeNormNLP : negativeNorm := by
  hypograph t
  nlp

#printp negativeNormNLP

example : GlobalEquivalence negativeNorm negativeNormNLP := negativeNormNLP.equivalence
example : IsSmoothNLP negativeNormNLP := negativeNormNLP.isSmoothNLP

end
end Examples.GettingStarted.GraphImpl
