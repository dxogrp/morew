/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Huber loss

The Huber loss is quadratic on `[-M, M]` and linear outside this interval.
For `M ≥ 0`, it is the attained minimum of `z² + 2M|x-z|` over real `z`.
The normalization gives `x²` in the quadratic region, and the loss is zero
everywhere when `M = 0`.
-/

@[expose] public section

namespace Morew.Fn

/-- Huber loss with quadratic branch `x²`. The attained-minimum and epigraph
representations require `M ≥ 0`. -/
noncomputable def huber (M x : ℝ) : ℝ :=
  if |x| ≤ M then x ^ 2 else 2 * M * |x| - M ^ 2

/-- Huber loss is quadratic between the joining points. -/
theorem huber_of_abs_le (M x : ℝ) (hx : |x| ≤ M) : huber M x = x ^ 2 := by
  simp only [huber, ite_eq_left hx]

/-- Huber loss is linear in the absolute residual outside the quadratic region. -/
theorem huber_of_abs_gt (M x : ℝ) (hx : M < |x|) :
    huber M x = 2 * M * |x| - M ^ 2 := by
  simp only [huber, ite_eq_right hx.not_ge]

/-- Huber loss is an even function of the residual. -/
@[simp] theorem huber_neg (M x : ℝ) : huber M (-x) = huber M x := by
  simp only [huber, abs_neg, neg_sq]

/-- A zero threshold gives the zero loss on every residual. -/
@[simp] theorem huber_zero_left (x : ℝ) : huber 0 x = 0 := by
  unfold huber
  split_ifs with hx
  · have hx₀ : x = 0 := abs_nonpos_iff.mp hx
    simp [hx₀]
  · ring

/-- The loss at a zero residual is zero for a nonnegative threshold. -/
@[simp] theorem huber_zero_right (M : ℝ) (hM : 0 ≤ M) : huber M 0 = 0 := by
  simp [huber, hM]

/-- The positive joining point has loss `M²`. -/
@[simp] theorem huber_self (M : ℝ) (hM : 0 ≤ M) : huber M M = M ^ 2 :=
  huber_of_abs_le M M (by rw [abs_of_nonneg hM])

/-- The negative joining point has loss `M²`. -/
theorem huber_neg_self (M : ℝ) (hM : 0 ≤ M) : huber M (-M) = M ^ 2 := by
  rw [huber_neg, huber_self M hM]

/-- Every value of `z² + 2M|x-z|` bounds Huber loss from above. -/
theorem huber_le_square_add_abs (M x z : ℝ) (hM : 0 ≤ M) :
    huber M x ≤ z ^ 2 + 2 * M * |x - z| := by
  by_cases hx : |x| ≤ M
  · rw [huber_of_abs_le M x hx]
    have hprod : x * (x - z) ≤ M * |x - z| := calc
      x * (x - z) ≤ |x * (x - z)| := le_abs_self _
      _ = |x| * |x - z| := abs_mul _ _
      _ ≤ M * |x - z| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    nlinarith [sq_nonneg (x - z)]
  · rw [huber_of_abs_gt M x (lt_of_not_ge hx)]
    by_cases hx₀ : 0 ≤ x
    · rw [abs_of_nonneg hx₀]
      have hbound := mul_le_mul_of_nonneg_left (le_abs_self (x - z)) hM
      nlinarith [sq_nonneg (z - M)]
    · rw [abs_of_neg (lt_of_not_ge hx₀)]
      have hbound := mul_le_mul_of_nonneg_left (neg_le_abs (x - z)) hM
      nlinarith [sq_nonneg (z + M)]

/-- Clamping the residual to `[-M, M]` attains the minimum of
`z² + 2M|x-z|`. The minimizing value is `-M`, `x`, or `M` in the three regions. -/
theorem huber_eq_square_add_abs_clamp (M x : ℝ) (hM : 0 ≤ M) :
    huber M x = (max (-M) (min M x)) ^ 2 +
      2 * M * |x - max (-M) (min M x)| := by
  by_cases hx : |x| ≤ M
  · obtain ⟨hl, hu⟩ := abs_le.mp hx
    rw [huber_of_abs_le M x hx, min_eq_right hu, max_eq_right hl]
    simp
  · rw [huber_of_abs_gt M x (lt_of_not_ge hx)]
    by_cases hx₀ : 0 ≤ x
    · have hMx : M ≤ x := (lt_of_not_ge hx).le.trans_eq (abs_of_nonneg hx₀)
      rw [min_eq_left hMx, max_eq_right (neg_le_self hM), abs_of_nonneg hx₀,
        abs_of_nonneg (sub_nonneg.mpr hMx)]
      ring
    · have hxM : x ≤ -M := by
        have h := lt_of_not_ge hx
        rw [abs_of_neg (lt_of_not_ge hx₀)] at h
        linarith
      rw [min_eq_right (hxM.trans (neg_le_self hM)), max_eq_left hxM,
        abs_of_neg (lt_of_not_ge hx₀), abs_of_nonpos (by linarith : x - -M ≤ 0)]
      ring

/-- Huber loss is nonnegative for a nonnegative threshold. -/
theorem huber_nonneg (M x : ℝ) (hM : 0 ≤ M) : 0 ≤ huber M x := by
  rw [huber_eq_square_add_abs_clamp M x hM]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) hM) (abs_nonneg _))

/-- An exact epigraph using a square bound and two absolute-residual bounds. -/
theorem huber_le_iff (M x t : ℝ) (hM : 0 ≤ M) :
    huber M x ≤ t ↔ ∃ z s r : ℝ,
      z ^ 2 ≤ s ∧ -r ≤ x - z ∧ x - z ≤ r ∧ s + 2 * M * r ≤ t := by
  constructor
  · intro h
    let z := max (-M) (min M x)
    refine ⟨z, z ^ 2, |x - z|, le_rfl, neg_abs_le _, le_abs_self _, ?_⟩
    exact (huber_eq_square_add_abs_clamp M x hM).symm.le.trans h
  · rintro ⟨z, s, r, hs, hl, hu, ht⟩
    have hr : |x - z| ≤ r := abs_le.mpr ⟨hl, hu⟩
    calc
      huber M x ≤ z ^ 2 + 2 * M * |x - z| := huber_le_square_add_abs M x z hM
      _ ≤ s + 2 * M * r := add_le_add hs
        (mul_le_mul_of_nonneg_left hr (mul_nonneg (by norm_num) hM))
      _ ≤ t := ht

end Morew.Fn
