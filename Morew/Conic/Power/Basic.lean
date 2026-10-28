/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Cone
import Mathlib.Tactic.FieldSimp

/-!
# Exact power-cone representations

Positive powers greater than one have an epigraph on nonnegative inputs;
negative powers have an epigraph on strictly positive inputs. Powers between
zero and one and binary weighted geometric means have hypographs on
nonnegative inputs. Their auxiliary nonnegative scalar preserves negative
lower bounds, which direct membership with the lower bound would exclude.
-/

namespace Morew.Conic.Power

/-- A power greater than one yields a valid reciprocal cone parameter. -/
theorem inverse_exponent_range (p : ℝ) (hp : 1 < p) :
    0 < 1 / p ∧ 1 / p < 1 := by
  have hp₀ : 0 < p := zero_lt_one.trans hp
  exact ⟨one_div_pos.mpr hp₀, (div_lt_one hp₀).mpr hp⟩

/-- A negative power yields a valid cone parameter for its epigraph. -/
theorem negative_exponent_range (p : ℝ) (hp : p < 0) :
    0 < 1 / (1 - p) ∧ 1 / (1 - p) < 1 :=
  inverse_exponent_range (1 - p) (by linarith)

/-- A real power greater than one has this exact epigraph on nonnegative inputs. -/
theorem rpow_le_iff (x t p : ℝ) (hx : 0 ≤ x) (hp : 1 < p) :
    x ^ p ≤ t ↔ (t, 1, x) ∈ POW (1 / p) := by
  rw [Cone.mem_powerSet]
  simp only [zero_le_one, Real.one_rpow, mul_one, abs_of_nonneg hx, true_and, one_div]
  have hp₀ : 0 < p := zero_lt_one.trans hp
  constructor
  · intro h
    have ht : 0 ≤ t := (Real.rpow_nonneg hx p).trans h
    exact ⟨ht, (Real.le_rpow_inv_iff_of_pos hx ht hp₀).mpr h⟩
  · rintro ⟨ht, h⟩
    exact (Real.le_rpow_inv_iff_of_pos hx ht hp₀).mp h

/-- A weighted geometric-mean hypograph retains arbitrary real lower bounds.
The auxiliary scalar is nonnegative, while the bound itself need not be. -/
theorem le_weightedGeomMean_iff (x y t α : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (_hα : 0 < α ∧ α < 1) :
    t ≤ x ^ α * y ^ (1 - α) ↔
      ∃ u : ℝ, 0 ≤ u ∧ t ≤ u ∧ (x, y, u) ∈ POW α := by
  have hf : 0 ≤ x ^ α * y ^ (1 - α) :=
    mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)
  constructor
  · intro h
    refine ⟨x ^ α * y ^ (1 - α), hf, h, ?_⟩
    exact ⟨hx, hy, (abs_of_nonneg hf).le⟩
  · rintro ⟨u, hu, htu, _, _, huf⟩
    exact htu.trans ((abs_of_nonneg hu) ▸ huf)

/-- A power between zero and one has an exact hypograph, including negative bounds. -/
theorem le_rpow_iff (x t p : ℝ) (hx : 0 ≤ x) (hp : 0 < p ∧ p < 1) :
    t ≤ x ^ p ↔ ∃ u : ℝ, 0 ≤ u ∧ t ≤ u ∧ (x, 1, u) ∈ POW p := by
  simpa only [Real.one_rpow, mul_one] using
    le_weightedGeomMean_iff x 1 t p hx zero_le_one hp

private theorem one_le_power_product_iff (x t p : ℝ) (hx : 0 < x)
    (ht : 0 ≤ t) (hp : p < 0) :
    1 ≤ t ^ (1 / (1 - p)) * x ^ (1 - 1 / (1 - p)) ↔ x ^ p ≤ t := by
  have hq : 0 < 1 - p := by linarith
  have hexp : (1 - 1 / (1 - p)) * (1 - p) = -p := by
    field_simp
    ring
  have hprod : (t ^ (1 / (1 - p)) * x ^ (1 - 1 / (1 - p))) ^ (1 - p) =
      t * x ^ (-p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg ht _) (Real.rpow_nonneg hx.le _),
      ← Real.rpow_mul ht, ← Real.rpow_mul hx.le,
      div_mul_cancel₀ 1 hq.ne', Real.rpow_one, hexp]
  rw [← Real.rpow_le_rpow_iff (by norm_num : (0 : ℝ) ≤ 1)
      (mul_nonneg (Real.rpow_nonneg ht _) (Real.rpow_nonneg hx.le _)) hq,
    Real.one_rpow, hprod]
  have hcancel : x ^ p * x ^ (-p) = 1 := by
    rw [← Real.rpow_add hx, add_neg_cancel, Real.rpow_zero]
  rw [← hcancel, mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hx (-p))]

/-- Negative real powers have this exact epigraph on strictly positive inputs.
At zero, native real exponentiation is totalized and this equivalence fails. -/
theorem rpow_neg_le_iff (x t p : ℝ) (hx : 0 < x) (hp : p < 0) :
    x ^ p ≤ t ↔ (t, x, 1) ∈ POW (1 / (1 - p)) := by
  rw [Cone.mem_powerSet]
  simp only [hx.le, true_and, abs_one]
  constructor
  · intro h
    have ht : 0 ≤ t := (Real.rpow_nonneg hx.le p).trans h
    exact ⟨ht, (one_le_power_product_iff x t p hx ht hp).mpr h⟩
  · rintro ⟨ht, h⟩
    exact (one_le_power_product_iff x t p hx ht hp).mp h

end Morew.Conic.Power
