/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Fn.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact squared Euclidean-norm representations

A native Euclidean norm bound is replaced by a nonnegative scalar bound and a
squared-norm inequality. These ordinary polynomial targets are separate from the
second-order-cone representations used by conic rewriting.

`euclideanNormEpigraph` defines the native target. The vector-specific
`norm2Epigraph` forwards to it and remains available for explicit `using`
selection; automatic rewriting registers only the general native record.
-/

namespace Morew.Rewrite

/-- A Euclidean norm bound is exactly a nonnegative bound and a polynomial row. -/
theorem norm2_le_iff {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ 0 ≤ t ∧ (∑ i, v i ^ 2) ≤ t ^ 2 := by
  have hnorm := norm_nonneg (WithLp.toLp 2 v)
  have hsq : ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
    simpa only [PiLp.toLp_apply] using EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)
  constructor
  · intro h
    have ht := hnorm.trans h
    exact ⟨ht, hsq ▸ (sq_le_sq₀ hnorm ht).mpr h⟩
  · rintro ⟨ht, h⟩
    exact (sq_le_sq₀ hnorm ht).mp (hsq.symm ▸ h)

/-- Native Euclidean-space values use their ordinary coordinates in the target. -/
noncomputable def euclideanNormEpigraph {n : Nat} :
    EpigraphRepresentation (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖) where
  Auxiliary := Unit
  target v t _ := 0 ≤ t ∧ (∑ i, (WithLp.ofLp v i) ^ 2) ≤ t ^ 2
  source_iff_exists v t := by
    simpa only [exists_const] using norm2_le_iff (WithLp.ofLp v) t

/-- The vector-specific native epigraph forwards to the Euclidean-space record. -/
noncomputable def norm2Epigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp 2 v‖) where
  Auxiliary := (euclideanNormEpigraph (n := n)).Auxiliary
  target v t u := euclideanNormEpigraph.target (WithLp.toLp 2 v) t u
  source_iff_exists v t :=
    euclideanNormEpigraph.source_iff_exists (WithLp.toLp 2 v) t

/-- The named Euclidean norm has the same two polynomial epigraph inequalities. -/
noncomputable def fnNorm2Epigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => Fn.norm2 v) :=
  norm2Epigraph

end Morew.Rewrite
