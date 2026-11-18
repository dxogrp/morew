/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Fn.Matrix
public import Morew.Conic.PSD
import Mathlib.Analysis.Matrix.Order

/-!
# Exact eigenvalue bounds

For a symmetric matrix of positive dimension, an upper bound on its largest
eigenvalue is equivalent to positive semidefiniteness of `t I - A`. A lower bound
on its smallest eigenvalue is equivalent to positive semidefiniteness of `A - t I`.
-/

@[expose] public section

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

/-- A smallest-eigenvalue lower bound is an exact affine PSD inequality. -/
theorem le_lambdaMin_iff {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hn : 0 < n) (t : ℝ) :
    t ≤ Fn.lambdaMin A ↔ (A - t • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  rw [Fn.lambdaMin_eq_neg_lambdaMax, le_neg, lambdaMax_le_iff (-A) hA.neg hn (-t)]
  simp only [neg_smul, sub_eq_add_neg, neg_neg, add_comm]

end Morew.Conic.Spectral
