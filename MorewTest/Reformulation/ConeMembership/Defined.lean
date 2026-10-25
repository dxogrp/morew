/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! Applied affine families with distinct aliases crossing a module boundary. -/

namespace MorewTest.Reformulation.ConeMembership.Defined

open Morew
noncomputable section

def shifted (offset x : ℝ) : ℝ := x + offset

def source (offset : ℝ) :=
  problem (x : ℝ)
    let first := shifted offset x
    let second := shifted offset x
    let unused := x - offset
    minimize first
    subject to
      grouped : (0 ≤ first ∧ True) ∧ second ≤ 4
      same : first = second

section
variable (offset : ℝ)

reformulation target : (source offset) := by
  conic

example : GlobalEquivalence (source offset) (target offset) := target.equivalence offset
example : (target.conicForm offset).data.toProblem = target offset :=
  (target.conicForm offset).represents

end
end
end MorewTest.Reformulation.ConeMembership.Defined
