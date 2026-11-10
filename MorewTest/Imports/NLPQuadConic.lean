/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP
import Morew.Reformulation.QuadConic

namespace MorewTest.Imports.NLPQuadConic
open Morew
noncomputable section

def source := problem (x : ℝ) minimize x ^ 2 subject to bound : x ≤ 2
reformulation quadratic : source := by qconic
reformulation smooth : source := by nlp
example : IsQuadConic quadratic := quadratic.isQuadConic
example : IsSmoothNLP smooth := smooth.isSmoothNLP

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 1 do
    Lean.throwError "NLP and quadratic imports duplicated presentation providers"

end
end MorewTest.Imports.NLPQuadConic
