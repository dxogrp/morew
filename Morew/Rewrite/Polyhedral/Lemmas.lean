/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact polyhedral bounds

Scalar and coordinatewise inequalities for absolute values, extrema, and vector
norms. The norm bounds retain their scalar condition in dimension zero.
-/

namespace Morew.Rewrite.Polyhedral

open scoped ENNReal

/-- Positive part retains the nonnegative bound as a separate inequality. -/
theorem posPart_le_iff (a t : ℝ) : a⁺ ≤ t ↔ a ≤ t ∧ 0 ≤ t := by
  rw [posPart_def, sup_le_iff]

/-- Reindex a maximum over a nonempty finite support as a coordinatewise inequality. -/
theorem sup'_le_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    s.sup' hs f ≤ t ↔
      (fun j : Fin s.card => f (s.equivFin.symm j)) ≤ (fun _ => t) := by
  rw [Finset.sup'_le_iff, ← s.forall_coe (fun i => f i ≤ t)]
  exact s.equivFin.forall_congr_left

/-- Reindex a minimum over a nonempty finite support as a coordinatewise inequality. -/
theorem le_inf'_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    t ≤ s.inf' hs f ↔
      (fun _ : Fin s.card => t) ≤ (fun j => f (s.equivFin.symm j)) := by
  rw [Finset.le_inf'_iff, ← s.forall_coe (fun i => t ≤ f i)]
  exact s.equivFin.forall_congr_left

/-- The standard norm of a finite real function is its infinity norm.
The explicit nonnegative bound makes the identity valid for `n = 0`. -/
theorem norm_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖v‖ ≤ t ↔ 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) := by
  rw [← and_iff_right_of_imp (fun h : ‖v‖ ≤ t => (norm_nonneg v).trans h)]
  apply and_congr_right
  intro ht
  simp only [pi_norm_le_iff_of_nonneg ht, Real.norm_eq_abs, abs_le',
    forall_and, Pi.le_def, Pi.neg_apply]

/-- The infinity-norm bound on `WithLp ∞` is equivalent to componentwise bounds. -/
theorem norm_toLp_top_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp ∞ v‖ ≤ t ↔
      0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) := by
  simpa only [PiLp.norm_toLp] using norm_le_iff v t

/-- An exact auxiliary-vector representation of a sum of absolute values.
The sum row becomes `0 ≤ t` when the dimension is zero. -/
theorem sum_abs_le_iff_exists {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    (∑ i, |v i|) ≤ t ↔
      ∃ u : Fin n → ℝ, v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t := by
  constructor
  · intro h
    refine ⟨fun i => |v i|, ?_, ?_, h⟩
    · intro i
      exact (abs_le'.mp le_rfl).1
    · intro i
      exact (abs_le'.mp le_rfl).2
  · rintro ⟨u, hp, hn, ht⟩
    refine le_trans (Finset.sum_le_sum ?_) ht
    intro i _hi
    exact abs_le'.mpr ⟨hp i, hn i⟩

/-- The one-norm epigraph represented by linear inequalities with an auxiliary vector. -/
theorem norm_toLp_one_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 1 v‖ ≤ t ↔
      ∃ u : Fin n → ℝ, v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t := by
  rw [PiLp.norm_eq_of_L1]
  simpa only [PiLp.toLp_apply, Real.norm_eq_abs] using sum_abs_le_iff_exists v t

end Morew.Rewrite.Polyhedral
