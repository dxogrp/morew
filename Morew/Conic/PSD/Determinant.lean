/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Determinant bounds for positive matrices

The determinant is monotone under positive-semidefinite perturbations of a
positive-definite real matrix. These lemmas also include empty dimensions.
-/

namespace Morew.Conic.LogDet

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency.types false in
/-- Every principal minor contributes nonnegatively to `det (I + H)` when `H`
is positive semidefinite, and the empty minor contributes one. -/
theorem one_le_det_one_add {n : Nat} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosSemidef) : 1 ≤ (1 + H).det := by
  classical
  have hexpand : (1 + H).det =
      ∑ s : Finset (Fin n), (H.submatrix (Subtype.val : s → Fin n) Subtype.val).det := by
    rw [add_comm]
    change detRowAlternating ((fun i => H i) + (fun i => (1 : Matrix (Fin n) (Fin n) ℝ) i)) = _
    rw [AlternatingMap.map_add_univ]
    apply Finset.sum_congr rfl
    intro s _
    exact det_piecewise_one_eq_submatrix_det H s
  rw [hexpand]
  calc
    1 = (H.submatrix (Subtype.val : (∅ : Finset (Fin n)) → Fin n) Subtype.val).det := by
      simp
    _ ≤ ∑ s : Finset (Fin n),
        (H.submatrix (Subtype.val : s → Fin n) Subtype.val).det :=
      Finset.single_le_sum (fun (s : Finset (Fin n)) _ =>
        (hH.submatrix (Subtype.val : s → Fin n)).det_nonneg)
        (Finset.mem_univ _)

/-- The determinant increases under a positive-semidefinite perturbation of a
positive-definite real matrix. -/
theorem det_le_det {n : Nat} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) : A.det ≤ B.det := by
  classical
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hSS : S * S = A := by
    simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hSu : IsUnit S := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hSd : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  let H := S⁻¹ * (B - A) * S⁻¹
  have hH : H.PosSemidef := by
    simpa only [hS.isHermitian.inv.eq] using hBA.mul_mul_conjTranspose_same S⁻¹
  have hfactor : S * (1 + H) * S = B := by
    calc
      S * (1 + H) * S = S * S + (S * S⁻¹) * (B - A) * (S⁻¹ * S) := by
        dsimp only [H]
        noncomm_ring
      _ = B := by rw [S.mul_nonsing_inv hSd, S.nonsing_inv_mul hSd, one_mul, mul_one, hSS]; abel
  calc
    A.det = S.det * S.det := by rw [← det_mul, hSS]
    _ ≤ S.det * S.det * (1 + H).det :=
      le_mul_of_one_le_right (mul_self_nonneg _) (one_le_det_one_add hH)
    _ = B.det := by rw [← hfactor, det_mul, det_mul]; ring

end Morew.Conic.LogDet
