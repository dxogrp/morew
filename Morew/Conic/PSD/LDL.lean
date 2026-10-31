/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Normalized real LDL factorization

The lower triangular factor in mathlib's LDL decomposition has unit diagonal.
These facts supply the attaining triangular witness for the log-determinant
representation, including for empty matrices.
-/

namespace Morew.Conic.LogDet

open Matrix InnerProductSpace

variable {n : Nat} {X : Matrix (Fin n) (Fin n) ℝ}

/-- The inverse lower factor in the LDL decomposition has unit diagonal. -/
theorem ldl_lowerInv_diag (hX : X.PosDef) (i : Fin n) : LDL.lowerInv hX i i = 1 := by
  let := X.transpose.toNormedAddCommGroup hX.transpose
  let := X.transpose.toInnerProductSpace hX.transpose.posSemidef
  have h := congrArg (fun v : Fin n → ℝ => v i)
    (gramSchmidt_def'' ℝ (Pi.basisFun ℝ (Fin n)) i)
  have hz : ∀ j ∈ Finset.Iio i,
      gramSchmidt ℝ (Pi.basisFun ℝ (Fin n)) j i = 0 := by
    intro j hj
    exact LDL.lowerInv_triangular hX (Finset.mem_Iio.mp hj)
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [Finset.sum_eq_zero (fun j hj => by rw [hz j hj, mul_zero]), add_zero] at h
  simpa only [LDL.lowerInv, Pi.basisFun_apply, Pi.single_eq_same] using h.symm

/-- The lower factor in the LDL decomposition is lower triangular. -/
theorem ldl_lower_triangular (hX : X.PosDef) : (LDL.lower hX).IsLowerTriangular := by
  apply Matrix.blockTriangular_inv_of_blockTriangular
  intro i j hij
  exact LDL.lowerInv_triangular hX hij

/-- The lower factor in the LDL decomposition has unit diagonal. -/
theorem ldl_lower_diag (hX : X.PosDef) (i : Fin n) : LDL.lower hX i i = 1 := by
  have h := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i i)
    (Matrix.inv_mul_of_invertible (LDL.lowerInv hX))
  simp only [Matrix.one_apply_eq] at h
  change (LDL.lower hX * LDL.lowerInv hX) i i = 1 at h
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
  · simpa only [ldl_lowerInv_diag, mul_one] using h
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [LDL.lowerInv_triangular hX hj, mul_zero]
    · rw [ldl_lower_triangular hX hj, zero_mul]
  · simp

/-- Every diagonal entry in the LDL decomposition is positive. -/
theorem ldl_diag_pos (hX : X.PosDef) (i : Fin n) : 0 < LDL.diagEntries hX i := by
  have hD : (LDL.diag hX).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff
      (isUnit_of_invertible (LDL.lowerInv hX))).mpr hX
  simpa only [LDL.diag, Matrix.diagonal_apply_eq] using hD.diag_pos (i := i)

/-- A positive-definite real matrix has a unit lower triangular LDL factorization. -/
theorem exists_lower_diagonal_factor (hX : X.PosDef) :
    ∃ (L : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
      L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧ (∀ i, 0 < d i) ∧
        L * Matrix.diagonal d * L.transpose = X := by
  refine ⟨LDL.lower hX, LDL.diagEntries hX, ldl_lower_triangular hX,
    ldl_lower_diag hX, ldl_diag_pos hX, ?_⟩
  simpa only [LDL.diag, Matrix.conjTranspose_eq_transpose_of_trivial] using
    LDL.lower_conj_diag hX

/-- A normalized LDL factorization expresses the determinant as the diagonal product. -/
theorem det_eq_prod_of_lower_diagonal_factor
    {L : Matrix (Fin n) (Fin n) ℝ} {d : Fin n → ℝ}
    (hL : L.IsLowerTriangular) (hdiag : ∀ i, L i i = 1)
    (hfactor : L * Matrix.diagonal d * L.transpose = X) : X.det = ∏ i, d i := by
  have hdet : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L hL]
    simp [hdiag]
  rw [← hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal, hdet, one_mul, mul_one]

end Morew.Conic.LogDet
