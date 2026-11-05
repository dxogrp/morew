/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

namespace MorewTest.Imports.Reformulation
open Morew
noncomputable section

def source := problem (x : ℝ) minimize x subject to
    first : |x| ≤ 2
    second : |x| ≤ 3
reformulation targeted : source := by
  conic at first
  nlp at second
reformulation asConic : targeted := by conic
reformulation asNLP : targeted := by nlp
example : IsConic asConic := asConic.isConic
example : IsSmoothNLP asNLP := asNLP.isSmoothNLP
example : GlobalEquiv source asConic := targeted.equiv.trans asConic.equiv
example : GlobalEquiv source asNLP := targeted.equiv.trans asNLP.equiv
end
end MorewTest.Imports.Reformulation
