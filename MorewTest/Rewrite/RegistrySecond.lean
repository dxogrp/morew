/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Rewrite.RegistrySource

namespace MorewTest.Rewrite.RegistrySecond

/-- Independent imported registration used to check candidate-order invariance. -/
@[morew_nlp]
def second (c : ℝ) :
    Morew.EpigraphRepresentation (MorewTest.Rewrite.RegistrySource.shifted c) :=
  MorewTest.Rewrite.RegistrySource.Scoped.shiftedEpigraph c

end MorewTest.Rewrite.RegistrySecond
