/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP
import Morew.Reformulation.Conic

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 1 do
    Lean.throwError "unexpected selective-import presentation providers"

namespace MorewTest.Imports.NLPConic
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
example : GlobalEquivalence source asConic := targeted.equivalence.trans asConic.equivalence
example : GlobalEquivalence source asNLP := targeted.equivalence.trans asNLP.equivalence
end
end MorewTest.Imports.NLPConic
