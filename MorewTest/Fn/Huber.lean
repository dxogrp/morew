/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Fn.Huber
import Mathlib.Tactic.NormNum

/-!
# Huber loss semantics

Signed residuals check the quadratic and linear branches, their joining points,
and the zero-threshold case. The explicit minimizing values certify attainment.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Fn.Huber

open Morew

noncomputable section

example : Fn.huber 2 1 = 1 ∧ Fn.huber 2 (-1) = 1 := by
  norm_num [Fn.huber]

example : Fn.huber 2 3 = 8 ∧ Fn.huber 2 (-3) = 8 := by
  norm_num [Fn.huber]

example : Fn.huber 2 2 = 4 ∧ Fn.huber 2 (-2) = 4 := by
  norm_num [Fn.huber]

example : Fn.huber 2 0 = 0 := by simp

example (M : ℝ) (hM : 0 ≤ M) :
    Fn.huber M M = M ^ 2 ∧ Fn.huber M (-M) = M ^ 2 := by
  simp [hM]

example (M x : ℝ) (hM : 0 ≤ M) : 0 ≤ Fn.huber M x :=
  Fn.huber_nonneg M x hM

example (M x : ℝ) : Fn.huber M (-x) = Fn.huber M x := by simp

example (x : ℝ) : Fn.huber 0 x = 0 := by simp

example (x t : ℝ) : Fn.huber 0 x ≤ t ↔ 0 ≤ t := by simp

example (x : ℝ) : ¬ Fn.huber 0 x ≤ -1 := by simp

/-! A negative threshold is outside the representation domain. -/

example : Fn.huber (-1) 0 = -1 := by norm_num [Fn.huber]

/-! The minimum is attained at the residual inside the quadratic region. -/

example (M x : ℝ) (hM : 0 ≤ M) (hx : |x| ≤ M) :
    Fn.huber M x = x ^ 2 + 2 * M * |x - x| := by
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  simpa only [min_eq_right hu, max_eq_right hl] using
    Fn.huber_eq_square_add_abs_clamp M x hM

/-! Outside the region, the nearest joining point attains the minimum. -/

example (M x : ℝ) (hM : 0 ≤ M) (hx : M ≤ x) :
    Fn.huber M x = M ^ 2 + 2 * M * |x - M| := by
  simpa only [min_eq_left hx, max_eq_right (neg_le_self hM)] using
    Fn.huber_eq_square_add_abs_clamp M x hM

example (M x : ℝ) (hM : 0 ≤ M) (hx : x ≤ -M) :
    Fn.huber M x = (-M) ^ 2 + 2 * M * |x - -M| := by
  simpa only [min_eq_right (hx.trans (neg_le_self hM)), max_eq_left hx] using
    Fn.huber_eq_square_add_abs_clamp M x hM

example (M x : ℝ) (hM : 0 ≤ M) :
    ∃ z : ℝ, Fn.huber M x = z ^ 2 + 2 * M * |x - z| ∧
      ∀ w : ℝ, z ^ 2 + 2 * M * |x - z| ≤ w ^ 2 + 2 * M * |x - w| := by
  refine ⟨max (-M) (min M x), Fn.huber_eq_square_add_abs_clamp M x hM, ?_⟩
  intro w
  rw [← Fn.huber_eq_square_add_abs_clamp M x hM]
  exact Fn.huber_le_square_add_abs M x w hM

/-! The lifted epigraph includes zero threshold and negative bounds. -/

example (x t : ℝ) :
    (∃ z s r : ℝ, z ^ 2 ≤ s ∧ -r ≤ x - z ∧ x - z ≤ r ∧ s ≤ t) ↔ 0 ≤ t := by
  simpa only [Fn.huber_zero_left, mul_zero, zero_mul, add_zero] using
    (Fn.huber_le_iff 0 x t (le_refl 0)).symm

example (M x : ℝ) (hM : 0 ≤ M) :
    ¬ ∃ z s r : ℝ,
      z ^ 2 ≤ s ∧ -r ≤ x - z ∧ x - z ≤ r ∧ s + 2 * M * r ≤ -1 := by
  rw [← Fn.huber_le_iff M x (-1) hM]
  exact not_le.mpr (lt_of_lt_of_le (by norm_num) (Fn.huber_nonneg M x hM))

end
end MorewTest.Fn.Huber
