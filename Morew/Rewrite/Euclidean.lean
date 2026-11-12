/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Fn.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact squared Euclidean-norm representations

A Euclidean norm bound becomes a nonnegative scalar bound and a squared-norm
inequality.

`norm2Epigraph` represents the Euclidean norm; `fnNorm2Epigraph` gives the
corresponding representation for `Fn.norm2`.
-/

namespace Morew.Rewrite

/-- A Euclidean norm bound is exactly a nonnegative bound and a polynomial row. -/
theorem norm2_le_iff {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ 0 ≤ t ∧ (∑ i, v i ^ 2) ≤ t ^ 2 := by
  have hnorm := norm_nonneg (WithLp.toLp 2 v)
  have hsq : ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 :=
    Fn.norm2_sq_eq_sum v
  constructor
  · intro h
    have ht := hnorm.trans h
    exact ⟨ht, hsq ▸ (sq_le_sq₀ hnorm ht).mpr h⟩
  · rintro ⟨ht, h⟩
    exact (sq_le_sq₀ hnorm ht).mp (hsq.symm ▸ h)

/-- The Euclidean-space norm epigraph expressed in vector coordinates. -/
def norm2Epigraph {n : Nat} :
    EpigraphRepr (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖) where
  Auxiliary := Unit
  target v t _ := 0 ≤ t ∧ (∑ i, (WithLp.ofLp v i) ^ 2) ≤ t ^ 2
  source_iff_exists v t := by
    simpa only [exists_const] using norm2_le_iff (WithLp.ofLp v) t

/-- The named Euclidean norm has the same two polynomial epigraph inequalities. -/
def fnNorm2Epigraph {n : Nat} :
    EpigraphRepr (fun v : Fin n → ℝ => Fn.norm2 v) where
  Auxiliary := (norm2Epigraph (n := n)).Auxiliary
  target v t u := norm2Epigraph.target (WithLp.toLp 2 v) t u
  source_iff_exists v t :=
    norm2Epigraph.source_iff_exists (WithLp.toLp 2 v) t

end Morew.Rewrite
