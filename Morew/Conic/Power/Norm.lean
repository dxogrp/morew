/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Basic
import Morew.Rewrite.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Exact finite p-norm epigraphs

The source is the native `PiLp` norm, with its exact extended-nonnegative-real
exponent. A checked real exponent greater than one supplies the power-cone
parameter. The explicit nonnegative bound also covers empty coordinate spaces.
-/

namespace Morew.Conic.Power

open scoped ENNReal

private theorem power_membership_iff (q r t x : ℝ) (hq : 1 < q)
    (hr : 0 ≤ r) (ht : 0 ≤ t) :
    (r, t, x) ∈ POW (1 / q) ↔ |x| ^ q ≤ r * t ^ (q - 1) := by
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have hexp : (1 - 1 / q) * q = q - 1 := by
    field_simp
  have hproduct : (r ^ (1 / q) * t ^ (1 - 1 / q)) ^ q = r * t ^ (q - 1) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hr _) (Real.rpow_nonneg ht _),
      ← Real.rpow_mul hr, ← Real.rpow_mul ht,
      div_mul_cancel₀ 1 hq₀.ne', Real.rpow_one, hexp]
  rw [Cone.mem_powerSet, and_iff_right hr, and_iff_right ht]
  rw [← Real.rpow_le_rpow_iff (abs_nonneg x)
    (mul_nonneg (Real.rpow_nonneg hr _) (Real.rpow_nonneg ht _)) hq₀, hproduct]

private theorem bound_mul_rpow (q t : ℝ) (hq : 1 < q) (ht : 0 ≤ t) :
    t * t ^ (q - 1) = t ^ q := by
  calc
    t * t ^ (q - 1) = t ^ (1 : ℝ) * t ^ (q - 1) := by rw [Real.rpow_one]
    _ = t ^ (1 + (q - 1)) :=
      (Real.rpow_add_of_nonneg ht zero_le_one (sub_nonneg.mpr hq.le)).symm
    _ = t ^ q := by congr 1; ring

/-- The native finite p-norm has an exact power-cone epigraph, including empty
coordinate spaces, signed coordinates, and a zero upper bound. -/
theorem norm_toLp_le_iff {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal)
    (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp p v‖ ≤ t ↔
      ∃ r : Fin n → ℝ, 0 ≤ t ∧ (∑ i, r i) ≤ t ∧
        ∀ i, (r i, t, v i) ∈ POW (1 / p.toReal) := by
  have hp₀ : 0 < p.toReal := zero_lt_one.trans hp
  have hsum : 0 ≤ ∑ i, |v i| ^ p.toReal :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  rw [PiLp.norm_eq_sum hp₀]
  simp only [Real.norm_eq_abs]
  constructor
  · intro h
    have ht : 0 ≤ t := (Real.rpow_nonneg hsum _).trans h
    have hbound : (∑ i, |v i| ^ p.toReal) ≤ t ^ p.toReal :=
      (Real.rpow_inv_le_iff_of_pos hsum ht hp₀).mp (by simpa only [one_div] using h)
    by_cases ht₀ : t = 0
    · subst t
      refine ⟨fun _ => 0, le_rfl, by simp, fun i => ?_⟩
      apply (power_membership_iff p.toReal 0 0 (v i) hp le_rfl le_rfl).mpr
      have hi : |v i| ^ p.toReal ≤ ∑ j, |v j| ^ p.toReal :=
        Finset.single_le_sum (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
          (Finset.mem_univ i)
      simpa only [Real.zero_rpow hp₀.ne', zero_mul] using hi.trans hbound
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht₀)
      have hden : 0 < t ^ (p.toReal - 1) := Real.rpow_pos_of_pos htpos _
      refine ⟨fun i => |v i| ^ p.toReal / t ^ (p.toReal - 1), ht, ?_, fun i => ?_⟩
      · rw [← Finset.sum_div, div_le_iff₀ hden, bound_mul_rpow _ _ hp ht]
        exact hbound
      · apply (power_membership_iff p.toReal _ t (v i) hp
          (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hden.le) ht).mpr
        rw [div_mul_cancel₀ _ hden.ne']
  · rintro ⟨r, ht, hsumr, hcones⟩
    rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos hsum ht hp₀).mpr
    have hcoordinates : ∀ i, |v i| ^ p.toReal ≤ r i * t ^ (p.toReal - 1) := by
      intro i
      exact (power_membership_iff p.toReal (r i) t (v i) hp (hcones i).1 ht).mp
        (hcones i)
    calc
      (∑ i, |v i| ^ p.toReal) ≤ ∑ i, r i * t ^ (p.toReal - 1) :=
        Finset.sum_le_sum fun i _ => hcoordinates i
      _ = (∑ i, r i) * t ^ (p.toReal - 1) := (Finset.sum_mul ..).symm
      _ ≤ t * t ^ (p.toReal - 1) :=
        mul_le_mul_of_nonneg_right hsumr (Real.rpow_nonneg ht _)
      _ = t ^ p.toReal := bound_mul_rpow _ _ hp ht

/-- The native finite p-norm epigraph, represented with one auxiliary vector
and a finite family of power-cone memberships. -/
noncomputable def normEpigraph {n : ℕ} (p : ℝ≥0∞) (hp : 1 < p.toReal) :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp p v‖) where
  Auxiliary := Fin n → ℝ
  target v t r := 0 ≤ t ∧ (∑ i, r i) ≤ t ∧ ∀ i,
    (r i, t, v i) ∈ (Cone.power (1 / p.toReal) (inverse_exponent_range p.toReal hp)).carrier
  source_iff_exists v t := norm_toLp_le_iff p hp v t

end Morew.Conic.Power
