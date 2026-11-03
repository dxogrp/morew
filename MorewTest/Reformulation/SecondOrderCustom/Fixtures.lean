/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax
import Morew.Conic.SecondOrder.Representations
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Shared auxiliary second-order certificate and its source problem -/

namespace MorewTest.Reformulation.SecondOrderCustom

open Morew Morew.Conic

noncomputable section

def userSquare (x : ℝ) : ℝ := x ^ 2

def auxiliaryRule : ExactConstraintLift
    (fun point : ℝ × ℝ => userSquare point.1 ≤ point.2) where
  Auxiliary := ℝ
  target point u := u = point.1 ∧
    (let bound := point.2
     True ∧ (bound, 1 / 2, ![u]) ∈ (Cone.rotatedSecondOrder 1).carrier)
  source_iff_exists point := by
    simp only [true_and, exists_eq_left, userSquare]
    exact SecondOrder.square_le_iff point.1 point.2

def source :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      before : Real.exp x ≤ 100
      auxiliary : userSquare x ≤ y
      after : y ≤ 10

end
end MorewTest.Reformulation.SecondOrderCustom
