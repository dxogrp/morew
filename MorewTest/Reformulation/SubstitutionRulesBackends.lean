/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.SubstitutionRules

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.SubstitutionRules

open Morew
noncomputable section

-- Continued conic and NLP certification use the resulting semantic problem.
reformulation squaredConic : nonneg := by
  substitute x := u ^ 2
  epigraph t
  conic
example : IsConic squaredConic := squaredConic.isConic
example : GlobalEquiv nonneg squaredConic := squaredConic.equiv

reformulation squaredNLP : nonneg := by
  substitute x := u ^ 2
  nlp
example : IsSmoothNLP squaredNLP := squaredNLP.isSmoothNLP

end
end MorewTest.Reformulation.SubstitutionRules
