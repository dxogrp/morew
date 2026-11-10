/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.QuadConic
import Morew.Reformulation.NLP

namespace MorewTest.Imports.QuadConicNLP
open Morew
noncomputable section

def source := problem (x : ℝ) minimize (x - 1) ^ 2 subject to bound : |x| ≤ 2
reformulation quadratic : source := by qconic
reformulation smooth : source := by nlp
example : IsQuadConic quadratic := quadratic.isQuadConic
example : IsSmoothNLP smooth := smooth.isSmoothNLP

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 1 do
    Lean.throwError "quadratic and NLP imports duplicated presentation providers"

end
end MorewTest.Imports.QuadConicNLP
