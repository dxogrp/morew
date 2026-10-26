/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Separately compiled problem families used by targeted NLP regressions -/

namespace MorewTest.Reformulation.NLPImportedSource

open Morew
noncomputable section

def family (radius : ℝ) :=
  problem (x : ℝ)
    let first := x ^ 2
    let second := x ^ 2
    minimize first + second
    subject to
      lower : radius ≤ x
      magnitude : |Real.log x| ≤ 5
      untouched : first ≤ second + 1

end
end MorewTest.Reformulation.NLPImportedSource
