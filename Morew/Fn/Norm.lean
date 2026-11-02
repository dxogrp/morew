/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Named real vector norms

These functions fix the usual one-, two-, and infinity-norms on ordinary finite
real vectors. Their meanings do not depend on a caller's local norm instances or
scopes. Each norm is zero on an empty vector.
-/

namespace Morew.Fn

/-- The sum of the absolute values of the coordinates. -/
noncomputable def norm1 {n : Nat} (x : Fin n → ℝ) : ℝ :=
  ‖WithLp.toLp 1 x‖

/-- The Euclidean norm: the square root of the sum of squared coordinates. -/
noncomputable def norm2 {n : Nat} (x : Fin n → ℝ) : ℝ :=
  ‖WithLp.toLp 2 x‖

/-- The maximum absolute coordinate, with value zero on an empty vector. -/
noncomputable def normInf {n : Nat} (x : Fin n → ℝ) : ℝ :=
  ‖x‖

theorem norm1_nonneg {n : Nat} (x : Fin n → ℝ) : 0 ≤ norm1 x :=
  norm_nonneg _

theorem norm2_nonneg {n : Nat} (x : Fin n → ℝ) : 0 ≤ norm2 x :=
  norm_nonneg _

theorem normInf_nonneg {n : Nat} (x : Fin n → ℝ) : 0 ≤ normInf x :=
  norm_nonneg _

@[simp] theorem norm1_zero {n : Nat} : norm1 (0 : Fin n → ℝ) = 0 := by
  simp [norm1]

@[simp] theorem norm2_zero {n : Nat} : norm2 (0 : Fin n → ℝ) = 0 := by
  simp [norm2]

@[simp] theorem normInf_zero {n : Nat} : normInf (0 : Fin n → ℝ) = 0 := by
  simp [normInf]

@[simp] theorem norm1_empty (x : Fin 0 → ℝ) : norm1 x = 0 := by
  rw [Subsingleton.elim x 0]
  exact norm1_zero

@[simp] theorem norm2_empty (x : Fin 0 → ℝ) : norm2 x = 0 := by
  rw [Subsingleton.elim x 0]
  exact norm2_zero

@[simp] theorem normInf_empty (x : Fin 0 → ℝ) : normInf x = 0 := by
  rw [Subsingleton.elim x 0]
  exact normInf_zero

/-- The one-norm is the sum of the absolute coordinate values. -/
theorem norm1_eq_sum_abs {n : Nat} (x : Fin n → ℝ) :
    norm1 x = ∑ i, |x i| := by
  simp only [norm1, PiLp.norm_eq_of_L1, Real.norm_eq_abs]

/-- The square of the Euclidean norm is the sum of squared coordinates. -/
theorem norm2_sq_eq_sum {n : Nat} (x : Fin n → ℝ) :
    norm2 x ^ 2 = ∑ i, x i ^ 2 := by
  simp only [norm2, PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

end Morew.Fn
