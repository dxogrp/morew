/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Shared problem declarations

Source declarations for reformulation and diagnostic tests.
-/

namespace MorewTest.Surface

open Morew
noncomputable section

def original :=
  problem (x : ℝ)
    minimize (Real.log x)^2
    subject to
      positive : 0 < x

def boundedMaximum :=
  problem (x y : ℝ)
    maximize x^2 - y^2
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

def identitySource :=
  problem (x : ℝ)
    minimize x ^ 2

end
end MorewTest.Surface
