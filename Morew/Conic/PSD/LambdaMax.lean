/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Fn.Matrix
import Morew.Conic.PSD
import Mathlib.Analysis.Matrix.Order

/-!
# Exact largest-eigenvalue epigraph

The source is the supremum of the real spectrum on a symmetric matrix of
positive dimension. The target preserves the original entries in `t I - A`.
-/

namespace Morew.Conic.Spectral

open Matrix

/-- A largest-eigenvalue upper bound is an exact affine PSD inequality. -/
theorem lambdaMax_le_iff {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hn : 0 < n) (t : ℝ) :
    Fn.lambdaMax A ≤ t ↔ (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  have hnonempty : (spectrum ℝ A).Nonempty := by
    rw [hH.spectrum_real_eq_range_eigenvalues]
    exact Set.range_nonempty _
  have hshift : (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A).IsHermitian :=
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t)).sub hH
  have hspectrum : spectrum ℝ (t • (1 : Matrix (Fin n) (Fin n) ℝ) - A) =
      (fun x => t - x) '' spectrum ℝ A := by
    simpa [Algebra.algebraMap_eq_smul_one, Set.singleton_sub] using
      (spectrum.singleton_sub_eq A t).symm
  rw [Fn.lambdaMax, csSup_le_iff A.finite_real_spectrum.bddAbove hnonempty,
    Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg, and_iff_right hshift,
    hspectrum]
  constructor
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact sub_nonneg.mpr (h x hx)
  · intro h x hx
    exact sub_nonneg.mp (h ⟨x, hx, rfl⟩)

end Morew.Conic.Spectral
