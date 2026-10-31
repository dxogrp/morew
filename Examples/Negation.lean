/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Exact bounds and graphs through negation

Negating a represented function exchanges its epigraph and hypograph rules.
Conic and smooth NLP rewrites share these identities, and graph records also
support signed equations.
-/

namespace Examples.Negation

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

-- Smooth NLPs can keep the logarithm itself; no conic decomposition is needed.
reformulation negativeLogNLP : negativeLog := by nlp

example : IsSmoothNLP negativeLogNLP := negativeLogNLP.isSmoothNLP

-- The same norm bound has a smooth polynomial representation for NLPs.
reformulation negativeNormNLP : negativeNorm := by
  hypograph t
  nlp

#printp negativeNormNLP

example : GlobalEquivalence negativeNorm negativeNormNLP := negativeNormNLP.equivalence
example : IsSmoothNLP negativeNormNLP := negativeNormNLP.isSmoothNLP

def negativeMinimum :=
  problem (x : ℝ)
    minimize -min (x ^ 2) (Real.sin x)

reformulation negativeMinimumNLP : negativeMinimum := by
  epigraph t
  nlp

#printp negativeMinimumNLP

example : GlobalEquivalence negativeMinimum negativeMinimumNLP := negativeMinimumNLP.equivalence
example : IsSmoothNLP negativeMinimumNLP := negativeMinimumNLP.isSmoothNLP

-- A downstream exact graph record can use smooth constraints for |x|.
@[morew_nlp]
def absoluteGraph : GraphRepresentation (fun x : ℝ => |x|) where
  Auxiliary := Unit
  target x y _ := 0 ≤ y ∧ y ^ 2 = x ^ 2
  source_iff_exists x y := by
    simp only [exists_const]
    constructor
    · rintro rfl
      exact ⟨abs_nonneg x, sq_abs x⟩
    · rintro ⟨hy, hsq⟩
      simpa only [abs_of_nonneg hy] using (sq_eq_sq_iff_abs_eq_abs y x).mp hsq

def signedGraph :=
  problem (x y : ℝ)
    minimize y
    subject to graph : y = -|x ^ 2 - 1|

reformulation signedGraphNLP : signedGraph := by nlp

#printp signedGraphNLP

example : GlobalEquivalence signedGraph signedGraphNLP := signedGraphNLP.equivalence
example : IsSmoothNLP signedGraphNLP := signedGraphNLP.isSmoothNLP

end
end Examples.Negation
