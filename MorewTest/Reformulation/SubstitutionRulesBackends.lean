/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.SubstitutionRules

/-! Backend integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.SubstitutionRules

open Morew
noncomputable section

-- Continued conic and NLP certification use the resulting semantic problem.
reformulation squaredConic : nonnegative := by
  substitute x := u ^ 2
  epigraph t
  conic
example : IsConic squaredConic := squaredConic.isConic
example : GlobalEquivalence nonnegative squaredConic := squaredConic.equivalence

reformulation squaredNLP : nonnegative := by
  substitute x := u ^ 2
  nlp
example : IsSmoothNLP squaredNLP := squaredNLP.isSmoothNLP

end
end MorewTest.Reformulation.SubstitutionRules
