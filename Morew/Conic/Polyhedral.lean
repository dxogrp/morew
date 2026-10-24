/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact polyhedral bounds

These identities express native real operations using scalar and coordinatewise
inequalities. They are independent of affine recognition and reformulation.
The norm bounds retain their scalar condition in dimension zero.
-/

namespace Morew.Conic.Polyhedral

open scoped ENNReal

/-- The epigraph of absolute value consists of two affine inequalities. -/
theorem abs_le_iff (a t : ℝ) : |a| ≤ t ↔ a ≤ t ∧ -a ≤ t :=
  abs_le'

/-- Positive part retains the nonnegative bound as a separate inequality. -/
theorem posPart_le_iff (a t : ℝ) : a⁺ ≤ t ↔ a ≤ t ∧ 0 ≤ t := by
  rw [posPart_def, sup_le_iff]

/-- A binary maximum is bounded above precisely when both operands are. -/
theorem max_le_iff (a b t : ℝ) : max a b ≤ t ↔ a ≤ t ∧ b ≤ t :=
  _root_.max_le_iff

/-- A binary minimum is bounded below precisely when both operands are. -/
theorem le_min_iff (a b t : ℝ) : t ≤ min a b ↔ t ≤ a ∧ t ≤ b :=
  _root_.le_min_iff

/-- Reindex a nonempty finite maximum into one coordinatewise inequality.
The ambient index type need not be finite. -/
theorem sup'_le_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    s.sup' hs f ≤ t ↔
      (fun j : Fin s.card => f (s.equivFin.symm j)) ≤ (fun _ => t) := by
  rw [Finset.sup'_le_iff]
  constructor
  · intro h j
    exact h _ (s.equivFin.symm j).property
  · intro h i hi
    simpa using h (s.equivFin ⟨i, hi⟩)

/-- Reindex a nonempty finite minimum into one coordinatewise inequality.
The ambient index type need not be finite. -/
theorem le_inf'_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    t ≤ s.inf' hs f ↔
      (fun _ : Fin s.card => t) ≤ (fun j => f (s.equivFin.symm j)) := by
  rw [Finset.le_inf'_iff]
  constructor
  · intro h j
    exact h _ (s.equivFin.symm j).property
  · intro h i hi
    simpa using h (s.equivFin ⟨i, hi⟩)

/-- The standard norm of a finite real function is its infinity norm.
The explicit nonnegative bound makes the identity valid for `n = 0`. -/
theorem norm_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖v‖ ≤ t ↔ 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) := by
  constructor
  · intro h
    have ht : 0 ≤ t := (norm_nonneg v).trans h
    have hv (i : Fin n) : v i ≤ t ∧ -v i ≤ t := by
      apply abs_le'.mp
      simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg ht).mp h i
    exact ⟨ht, fun i => (hv i).1, fun i => (hv i).2⟩
  · rintro ⟨ht, hp, hn⟩
    apply (pi_norm_le_iff_of_nonneg ht).mpr
    intro i
    simpa only [Real.norm_eq_abs] using abs_le'.mpr ⟨hp i, hn i⟩

/-- An explicit native infinity-norm carrier has the same polyhedral bound. -/
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

/-- The native finite one-norm has an exact auxiliary-vector representation. -/
theorem norm_toLp_one_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 1 v‖ ≤ t ↔
      ∃ u : Fin n → ℝ, v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t := by
  rw [PiLp.norm_eq_of_L1]
  simpa only [PiLp.toLp_apply, Real.norm_eq_abs] using sum_abs_le_iff_exists v t

end Morew.Conic.Polyhedral
