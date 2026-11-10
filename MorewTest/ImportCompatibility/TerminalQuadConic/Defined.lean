/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-! Quadratic forms retain curvature and constraint evidence across compilation. -/

namespace MorewTest.ImportCompatibility.TerminalQuadConic

open Morew
noncomputable section

variable (weight ε : ℝ) (hweight : 0 ≤ weight) (hε : 0 < ε)

def source (weight ε : ℝ) :=
  problem (x t : ℝ)
    minimize weight * (x - 2) ^ 2 + 3
    subject to
      logarithm : t ≤ Real.log x
      margin : ε ≤ x

include hweight hε in
reformulation target : (source weight ε) := by
  qconic

example : GlobalEquiv (source weight ε) (target weight ε) := target.equiv weight ε hε
example : IsQuadConic (target weight ε) := target.isQuadConic weight ε hweight

def maximum (weight : ℝ) :=
  problem (x : ℝ)
    maximize 5 - weight * x ^ 2

include hweight in
reformulation maximumTarget : (maximum weight) := by
  qconic

end
end MorewTest.ImportCompatibility.TerminalQuadConic
