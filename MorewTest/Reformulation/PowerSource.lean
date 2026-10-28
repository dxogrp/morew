/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Imported power models used by command integration tests -/

namespace MorewTest.Reformulation.PowerSource

open Morew

noncomputable section

def exponent : ℝ := 3 / 2

theorem exponent_range : 1 < exponent := by norm_num [exponent]

def source (offset : ℝ) :=
  problem (x t : ℝ)
    let base := x + offset
    let power := Real.rpow base exponent
    minimize t
    subject to
      before : 0 ≤ base
      bound : power ≤ t
      after : t ≤ 10

variable (offset : ℝ)

reformulation rewritten : (source offset) := by
  conic at bound using (Morew.Conic.Power.rpowEpigraph exponent exponent_range)

-- Numeric parameter normalization and its transported range proof survive imports.
def numericSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      positive : 1 ≤ x
      bound : x ^ (-1 / 2 : ℝ) ≤ t

reformulation numericTarget : numericSource := by
  conic at bound

end

end MorewTest.Reformulation.PowerSource
