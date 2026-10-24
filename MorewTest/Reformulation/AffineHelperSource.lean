/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Affine.HelperFixtures

/-!
# Imported model family with affine helper references

The consuming module must retain the family's local definition and labels when
certifying an applied source through bounded helper expansion.
-/

namespace MorewTest.Reformulation.AffineHelperSource

open Morew MorewTest.Affine.HelperFixtures

noncomputable def source (scale offset : ℝ) :=
  problem (x : ℝ)
    let loss := cost scale offset x
    minimize loss
    subject to
      cap : loss ≤ 10
      lower : 0 ≤ cost 1 0 x

end MorewTest.Reformulation.AffineHelperSource
