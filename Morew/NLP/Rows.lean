/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP.Basic
import Morew.NLP.Domain

/-!
# Smoothness evidence for generated constraint rows

These certificates describe only the supplied predicates. They make no claim
about an objective or any other constraints. Finite families stay grouped, and
each closed scalar comparison records smoothness of its exact difference.
-/

namespace Morew.NLP.Rows

/-- The exact upper-bound normalization recorded by a scalar row certificate. -/
theorem upper_residual_iff (lhs rhs : ℝ) :
    (Bounds.upperBound 0).Contains (lhs - rhs) ↔ lhs ≤ rhs := by
  rw [Bounds.contains_upperBound]
  exact sub_nonpos

/-- The exact lower-bound normalization recorded by a scalar row certificate. -/
theorem lower_residual_iff (lhs rhs : ℝ) :
    (Bounds.lowerBound 0).Contains (lhs - rhs) ↔ lhs ≥ rhs := by
  rw [Bounds.contains_lowerBound]
  exact sub_nonneg

/-- The exact equality normalization recorded by a scalar row certificate. -/
theorem fixed_residual_iff (lhs rhs : ℝ) :
    (Bounds.fixed 0).Contains (lhs - rhs) ↔ lhs = rhs := by
  rw [Bounds.contains_fixed]
  exact sub_eq_zero

/-- Canonical vector upper bounds are coordinatewise scalar bounds. -/
theorem vector_le_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs ≤ rhs ↔ ∀ i, lhs i ≤ rhs i := Iff.rfl

/-- Canonical vector lower bounds are coordinatewise scalar bounds. -/
theorem vector_ge_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs ≥ rhs ↔ ∀ i, lhs i ≥ rhs i := Iff.rfl

/-- Vector equality is exactly coordinatewise scalar equality. -/
theorem vector_eq_iff {n : ℕ} (lhs rhs : Fin n → ℝ) :
    lhs = rhs ↔ ∀ i, lhs i = rhs i := funext_iff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A predicate assembled from smooth closed scalar residuals on one domain. -/
inductive Certified (domain : Set X) : (X → Prop) → Prop where
  /-- The empty row imposes no condition. -/
  | truth : Certified domain (fun _ => True)
  /-- Both constituent rows use the same evaluation domain. -/
  | and {p q : X → Prop} : Certified domain p → Certified domain q →
      Certified domain (fun x => p x ∧ q x)
  /-- An upper bound has residual `lhs - rhs` bounded above by zero. -/
  | le (lhs rhs : X → ℝ)
      (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
      Certified domain (fun x => lhs x ≤ rhs x)
  /-- A lower bound has residual `lhs - rhs` bounded below by zero. -/
  | ge (lhs rhs : X → ℝ)
      (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
      Certified domain (fun x => lhs x ≥ rhs x)
  /-- Equality fixes the residual `lhs - rhs` at zero. -/
  | eq (lhs rhs : X → ℝ)
      (smooth : ContDiffOn ℝ 2 (fun x => lhs x - rhs x) domain) :
      Certified domain (fun x => lhs x = rhs x)
  /-- A symbolic finite family retains its coordinate predicates. -/
  | family {n : ℕ} (p : Fin n → X → Prop)
      (certified : ∀ i, Certified domain (p i)) :
      Certified domain (fun x => ∀ i, p i x)
  /-- Checked logical transport preserves the original row predicate. -/
  | of_iff (p q : X → Prop) (equivalent : ∀ x, p x ↔ q x)
      (certified : Certified domain q) : Certified domain p

/-- A generated row remains certified on a smaller common domain. -/
theorem Certified.mono {s t : Set X} {p : X → Prop}
    (certified : Certified s p) (subset : t ⊆ s) : Certified t p := by
  induction certified with
  | truth => exact .truth
  | and _ _ left right => exact .and left right
  | le lhs rhs smooth => exact .le lhs rhs (smooth.mono subset)
  | ge lhs rhs smooth => exact .ge lhs rhs (smooth.mono subset)
  | eq lhs rhs smooth => exact .eq lhs rhs (smooth.mono subset)
  | family p _ ih => exact .family p ih
  | of_iff p q equivalent _ ih => exact .of_iff p q equivalent ih

end Morew.NLP.Rows
