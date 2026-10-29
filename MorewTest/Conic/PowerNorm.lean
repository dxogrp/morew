/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Norm
import Mathlib.NumberTheory.Real.Irrational

/-!
# Exact native p-norm semantics

These tests check the representation independently of registry selection and
elaboration, including signed inputs, empty dimensions, zero bounds, and exact
rational and irrational exponents.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Conic.PowerNorm

open Morew Morew.Conic
open scoped ENNReal

noncomputable section

example {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal) :
    (Power.normEpigraph (n := n) p hp).Auxiliary = (Fin n → ℝ) := rfl

example {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal)
    (v r : Fin n → ℝ) (t : ℝ) :
    (Power.normEpigraph p hp).target v t r ↔
      0 ≤ t ∧ (∑ i, r i) ≤ t ∧ ∀ i, (r i, t, v i) ∈ POW (1 / p.toReal) := Iff.rfl

example {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal) (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp p v‖ ≤ t ↔ ∃ r, (Power.normEpigraph p hp).target v t r :=
  (Power.normEpigraph p hp).source_iff_exists v t

/-! Empty dimensions still require a nonnegative upper bound. -/

example (p : ℝ≥0∞) (hp : 1 < p.toReal) (t : ℝ) :
    (∃ r : Fin 0 → ℝ, 0 ≤ t ∧ (∑ i, r i) ≤ t ∧
      ∀ i, (r i, t, (0 : Fin 0 → ℝ) i) ∈ POW (1 / p.toReal)) ↔ 0 ≤ t := by
  rw [← Power.norm_toLp_le_iff p hp]
  rw [PiLp.norm_eq_sum (zero_lt_one.trans hp)]
  simp [Real.zero_rpow (inv_ne_zero (zero_lt_one.trans hp).ne')]

example (p : ℝ≥0∞) (hp : 1 < p.toReal) :
    ¬ ∃ r : Fin 0 → ℝ, (Power.normEpigraph p hp).target 0 (-1) r := by
  rintro ⟨r, h⟩
  have := h.1
  norm_num at this

/-! Zero vectors admit a zero bound at every supported exponent. -/

example {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal) :
    (Power.normEpigraph (n := n) p hp).target 0 0 (0 : Fin n → ℝ) := by
  refine ⟨le_rfl, by simp, fun i => ?_⟩
  exact Cone.zero_mem_powerSet _ (Power.inverse_exponent_range _ hp)

example {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal) (v : Fin n → ℝ)
    (h : ‖WithLp.toLp p v‖ ≤ 0) : v = 0 := by
  obtain ⟨r, _, _, hcones⟩ := (Power.norm_toLp_le_iff p hp v 0).mp h
  funext i
  exact ((Cone.mem_powerSet_zero_right _ _ _
    (Power.inverse_exponent_range _ hp)).mp (hcones i)).2

example {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal) (v : Fin n → ℝ) :
    ¬ ‖WithLp.toLp p v‖ ≤ -1 := by
  rw [Power.norm_toLp_le_iff p hp]
  rintro ⟨r, ht, _, _⟩
  norm_num at ht

/-! Rational powers act on absolute values, not nonnegative-only coordinates. -/

example : ∃ r : Fin 2 → ℝ,
    (Power.normEpigraph (3 / 2) (by norm_num)).target ![-1, 0] 1 r := by
  apply (Power.normEpigraph (3 / 2) (by norm_num)).source_iff_exists _ _ |>.mp
  norm_num [PiLp.norm_eq_sum (by norm_num : 0 < (3 / 2 : ℝ≥0∞).toReal),
    Fin.sum_univ_succ]

example : ∃ r : Fin 1 → ℝ,
    (Power.normEpigraph (3 / 2) (by norm_num)).target ![-4] 4 r := by
  apply (Power.normEpigraph (3 / 2) (by norm_num)).source_iff_exists _ _ |>.mp
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (3 / 2 : ℝ≥0∞).toReal)]
  simp only [Fin.sum_univ_one, Real.norm_eq_abs, Matrix.cons_val_zero, abs_neg,
    one_div]
  rw [Real.rpow_rpow_inv (by norm_num) (by norm_num)]
  norm_num

example : ∃ r : Fin 2 → ℝ,
    (Power.normEpigraph 3 (by norm_num)).target ![-2, 2] 3 r := by
  apply (Power.normEpigraph 3 (by norm_num)).source_iff_exists _ _ |>.mp
  rw [PiLp.norm_eq_sum (by norm_num : 0 < (3 : ℝ≥0∞).toReal)]
  norm_num [Fin.sum_univ_succ]
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num)
    (by norm_num : (0 : ℝ) < 3)).mpr
  norm_num

example {n : ℕ} (q : ℝ) (hq : 1 < q) (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp (ENNReal.ofReal q) v‖ ≤ t ↔
      ∃ r : Fin n → ℝ, 0 ≤ t ∧ (∑ i, r i) ≤ t ∧
        ∀ i, (r i, t, v i) ∈ POW (1 / q) := by
  have hp : 1 < (ENNReal.ofReal q).toReal := by
    simpa only [ENNReal.toReal_ofReal (zero_lt_one.trans hq).le] using hq
  simpa only [ENNReal.toReal_ofReal (zero_lt_one.trans hq).le] using
    Power.norm_toLp_le_iff (ENNReal.ofReal q) hp v t

/-! The irrational example retains sqrt(2) exactly in its cone parameter. -/

example : Irrational (Real.sqrt 2) := irrational_sqrt_two

private theorem sqrtTwoRange : 1 < (ENNReal.ofReal (Real.sqrt 2)).toReal := by
  simpa only [ENNReal.toReal_ofReal (Real.sqrt_nonneg 2)] using Real.one_lt_sqrt_two

example : ∃ r : Fin 1 → ℝ,
    (Power.normEpigraph (ENNReal.ofReal (Real.sqrt 2)) sqrtTwoRange).target ![-1] 1 r := by
  apply (Power.normEpigraph _ sqrtTwoRange).source_iff_exists _ _ |>.mp
  norm_num [PiLp.norm_eq_sum (zero_lt_one.trans sqrtTwoRange), Fin.sum_univ_succ]

example (r : Fin 1 → ℝ) :
    (Power.normEpigraph (ENNReal.ofReal (Real.sqrt 2)) sqrtTwoRange).target ![-1] 1 r ↔
      0 ≤ (1 : ℝ) ∧ (∑ i, r i) ≤ 1 ∧
        ∀ i, (r i, 1, (![-1] : Fin 1 → ℝ) i) ∈ POW (1 / Real.sqrt 2) := by
  change (0 ≤ (1 : ℝ) ∧ (∑ i, r i) ≤ 1 ∧
    ∀ i, (r i, 1, (![-1] : Fin 1 → ℝ) i) ∈
      POW (1 / (ENNReal.ofReal (Real.sqrt 2)).toReal)) ↔ _
  rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg 2)]

end

end MorewTest.Conic.PowerNorm
