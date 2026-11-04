/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform.Parameterization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Reusable coordinate substitution rules

Coordinate parameterizations with right inverses on specified ranges.
Coefficients may depend on unchanged coordinates; affine substitutions require
nonzero slopes at feasible points.
-/

namespace Morew.Substitution

universe u v

/-- The identity map covers every coordinate value. -/
def identity {R : Type u} {X : Type v} :
    CoordinateParameterization (fun (_ : R) (a : X) => a) where
  range _ _ := True
  preimage _ a := a.1
  rightInverse _ _ := rfl

/-- Negation covers every real coordinate. -/
noncomputable def neg {R : Type u} :
    CoordinateParameterization (fun (_ : R) (a : ℝ) => -a) where
  range _ _ := True
  preimage _ a := -a.1
  rightInverse _ a := neg_neg a.1

/-- Left multiplication covers every real value when the slope is nonzero. -/
noncomputable def mulLeft {R : Type u} (a : R → ℝ) :
    CoordinateParameterization (fun r u => a r * u) where
  range r _ := a r ≠ 0
  preimage r x := x.1 / a r
  rightInverse r x := by
    simp only [mul_div_cancel₀ _ x.2]

/-- Right multiplication with a nonzero slope. -/
noncomputable def mulRight {R : Type u} (a : R → ℝ) :
    CoordinateParameterization (fun r u => u * a r) where
  range r _ := a r ≠ 0
  preimage r x := x.1 / a r
  rightInverse _ x := div_mul_cancel₀ x.1 x.2

/-- Add an offset on the right. -/
noncomputable def addRight {R : Type u} (b : R → ℝ) :
    CoordinateParameterization (fun r u => u + b r) where
  range _ _ := True
  preimage r x := x.1 - b r
  rightInverse r x := sub_add_cancel x.1 (b r)

/-- Add an offset on the left. -/
noncomputable def addLeft {R : Type u} (b : R → ℝ) :
    CoordinateParameterization (fun r u => b r + u) where
  range _ _ := True
  preimage r x := x.1 - b r
  rightInverse r x := by
    rw [add_comm, sub_add_cancel]

/-- Subtract an offset from the new coordinate. -/
noncomputable def subRight {R : Type u} (b : R → ℝ) :
    CoordinateParameterization (fun r u => u - b r) where
  range _ _ := True
  preimage r x := x.1 + b r
  rightInverse r x := add_sub_cancel_right x.1 (b r)

/-- Subtract the new coordinate from an offset. -/
noncomputable def subLeft {R : Type u} (b : R → ℝ) :
    CoordinateParameterization (fun r u => b r - u) where
  range _ _ := True
  preimage r x := b r - x.1
  rightInverse r x := sub_sub_cancel (b r) x.1

/-- An affine coordinate map with a nonzero slope at each feasible point. -/
noncomputable def affine {R : Type u} (a b : R → ℝ) :
    CoordinateParameterization (fun r u => a r * u + b r) where
  range r _ := a r ≠ 0
  preimage r x := (x.1 - b r) / a r
  rightInverse r x := by
    rw [mul_div_cancel₀ _ x.2, sub_add_cancel]

/-- Exponentiation covers the strictly positive real values. -/
noncomputable def exp {R : Type u} :
    CoordinateParameterization (fun (_ : R) u => Real.exp u) where
  range _ x := 0 < x
  preimage _ x := Real.log x.1
  rightInverse _ x := Real.exp_log x.2

/-- Squaring covers the nonnegative reals using the nonnegative square root
as a preimage. -/
noncomputable def square {R : Type u} :
    CoordinateParameterization (fun (_ : R) (u : ℝ) => u ^ 2) where
  range _ x := 0 ≤ x
  preimage _ x := Real.sqrt x.1
  rightInverse _ x := Real.sq_sqrt x.2

end Morew.Substitution
