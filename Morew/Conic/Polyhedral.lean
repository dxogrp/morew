/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Polyhedral.Lemmas

/-!
# Exact polyhedral bounds

Compatibility theorem names for the shared identities in
`Morew.Rewrite.Polyhedral`. This import remains independent of representation
records and the modeling language.
-/

namespace Morew.Conic.Polyhedral

open scoped ENNReal

/-- The epigraph of absolute value consists of two affine inequalities. -/
theorem abs_le_iff (a t : ℝ) : |a| ≤ t ↔ a ≤ t ∧ -a ≤ t :=
  Morew.Rewrite.Polyhedral.abs_le_iff a t

/-- Positive part retains the nonnegative bound as a separate inequality. -/
theorem posPart_le_iff (a t : ℝ) : a⁺ ≤ t ↔ a ≤ t ∧ 0 ≤ t :=
  Morew.Rewrite.Polyhedral.posPart_le_iff a t

/-- A binary maximum is bounded above precisely when both operands are. -/
theorem max_le_iff (a b t : ℝ) : max a b ≤ t ↔ a ≤ t ∧ b ≤ t :=
  Morew.Rewrite.Polyhedral.max_le_iff a b t

/-- A binary minimum is bounded below precisely when both operands are. -/
theorem le_min_iff (a b t : ℝ) : t ≤ min a b ↔ t ≤ a ∧ t ≤ b :=
  Morew.Rewrite.Polyhedral.le_min_iff a b t

/-- Reindex a nonempty finite maximum into one coordinatewise inequality.
The ambient index type need not be finite. -/
theorem sup'_le_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    s.sup' hs f ≤ t ↔
      (fun j : Fin s.card => f (s.equivFin.symm j)) ≤ (fun _ => t) :=
  Morew.Rewrite.Polyhedral.sup'_le_iff s hs f t

/-- Reindex a nonempty finite minimum into one coordinatewise inequality.
The ambient index type need not be finite. -/
theorem le_inf'_iff {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    t ≤ s.inf' hs f ↔
      (fun _ : Fin s.card => t) ≤ (fun j => f (s.equivFin.symm j)) :=
  Morew.Rewrite.Polyhedral.le_inf'_iff s hs f t

/-- The standard norm of a finite real function is its infinity norm.
The explicit nonnegative bound makes the identity valid for `n = 0`. -/
theorem norm_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖v‖ ≤ t ↔ 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) :=
  Morew.Rewrite.Polyhedral.norm_le_iff v t

/-- An explicit native infinity-norm carrier has the same polyhedral bound. -/
theorem norm_toLp_top_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp ∞ v‖ ≤ t ↔
      0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) :=
  Morew.Rewrite.Polyhedral.norm_toLp_top_le_iff v t

/-- An exact auxiliary-vector representation of a sum of absolute values.
The sum row becomes `0 ≤ t` when the dimension is zero. -/
theorem sum_abs_le_iff_exists {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    (∑ i, |v i|) ≤ t ↔
      ∃ u : Fin n → ℝ, v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t :=
  Morew.Rewrite.Polyhedral.sum_abs_le_iff_exists v t

/-- The native finite one-norm has an exact auxiliary-vector representation. -/
theorem norm_toLp_one_le_iff {n : ℕ} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 1 v‖ ≤ t ↔
      ∃ u : Fin n → ℝ, v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t :=
  Morew.Rewrite.Polyhedral.norm_toLp_one_le_iff v t

end Morew.Conic.Polyhedral
