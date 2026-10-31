/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Conic bounds through negation

An epigraph bound on a negative concave function reuses its hypograph rule.
A hypograph bound on a negative convex function reuses its epigraph rule.
The original function's domain and norm remain part of the model.
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

end
end Examples.Negation
