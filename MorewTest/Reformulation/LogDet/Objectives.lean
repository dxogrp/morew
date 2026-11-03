/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.LogDet.Sources

/-! Log-det maximization and negative-log-det minimization compose objective introductions. -/

namespace MorewTest.Reformulation.LogDet

open Morew Morew.Conic

noncomputable section

def maximum :=
  problem (X : SymmetricMatrix 2)
    maximize Fn.logDet X.toMatrix
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

reformulation maximumTarget : maximum := by
  hypograph t as logDet_bound
  conic

def negativeMinimum :=
  problem (X : SymmetricMatrix 2)
    minimize -Fn.logDet X.toMatrix
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

reformulation negativeMinimumTarget : negativeMinimum := by
  epigraph t as logDet_bound
  conic

example : GlobalEquivalence maximum maximumTarget := maximumTarget.equivalence
example : IsConic maximumTarget := maximumTarget.isConic
example : GlobalEquivalence negativeMinimum negativeMinimumTarget :=
  negativeMinimumTarget.equivalence
example : IsConic negativeMinimumTarget := negativeMinimumTarget.isConic

end
end MorewTest.Reformulation.LogDet
