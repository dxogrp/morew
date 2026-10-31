/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD
import Morew.Conic.PSD.LDL
import Morew.Conic.PSD.Determinant
import Morew.Conic.PSD.Triangular
import Morew.Conic.Exponential
import Morew.Fn.Matrix

/-!
# Exact log-determinant hypographs

Lower triangular factors give an exact PSD/exponential representation of the
positive-definite log-determinant hypograph. The reverse implication proves
positive definiteness, rather than assuming a domain for the totalized logarithm.
-/

namespace Morew.Conic.LogDet

open Matrix

variable {n : Nat}

/-- A positive-definite matrix admits an attaining triangular PSD witness. -/
theorem exists_triangular_block {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ,
      Z.IsLowerTriangular ∧ (∀ i, 0 < Z i i) ∧
      (fromBlocksFin X Z Z.transpose (Matrix.diagonal (fun i => Z i i))).PosSemidef ∧
      X.det = ∏ i, Z i i := by
  obtain ⟨L, d, hL, hdiag, hd, hfactor⟩ := exists_lower_diagonal_factor hX
  let D := Matrix.diagonal d
  let Z := L * D
  have hD : D.PosDef := Matrix.PosDef.diagonal hd
  let := hD.isUnit.invertible
  have hZdiag : ∀ i, Z i i = d i := by
    intro i
    simp [Z, D, Matrix.mul_diagonal, hdiag]
  have hZ : Z.IsLowerTriangular := hL.mul (Matrix.blockTriangular_diagonal d)
  have hschur : Z * D⁻¹ * Z.transpose = X := by
    simpa only [Z, Matrix.transpose_mul, D, Matrix.diagonal_transpose,
      Matrix.mul_assoc, Matrix.inv_mul_cancel_left_of_invertible] using hfactor
  refine ⟨Z, hZ, fun i => hZdiag i ▸ hd i, ?_, ?_⟩
  · simp only [hZdiag]
    rw [posSemidef_fromBlocksFin_iff]
    have h := (Matrix.PosDef.fromBlocks₂₂ X Z hD).mpr
      (show (X - Z * D⁻¹ * Z.transpose).PosSemidef by
        rw [hschur, sub_self]
        exact Matrix.PosSemidef.zero)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  · simpa only [hZdiag] using det_eq_prod_of_lower_diagonal_factor hL hdiag hfactor

/-- Positive triangular diagonals and the PSD block force a positive-definite
matrix and bound the product of the diagonal by its determinant. -/
theorem posDef_and_prod_le_det_of_triangular_block
    {X Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.IsLowerTriangular)
    (hd : ∀ i, 0 < Z i i)
    (hblock : (fromBlocksFin X Z Z.transpose
      (Matrix.diagonal (fun i => Z i i))).PosSemidef) :
    X.PosDef ∧ (∏ i, Z i i) ≤ X.det := by
  let D := Matrix.diagonal (fun i => Z i i)
  have hD : D.PosDef := Matrix.PosDef.diagonal hd
  let := hD.isUnit.invertible
  have hprod : 0 < ∏ i, Z i i := Finset.prod_pos fun i _ => hd i
  have hdetZ : Z.det = ∏ i, Z i i := Matrix.det_of_isLowerTriangular Z hZ
  have hunit : IsUnit Z := Z.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr
    (hdetZ ▸ hprod.ne'))
  let Q := Z * D⁻¹ * Z.transpose
  have hQ : Q.PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using (Matrix.IsUnit.posDef_star_right_conjugate_iff hunit).mpr hD.inv
  have hdiff : (X - Q).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ X Z hD).mp
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (posSemidef_fromBlocksFin_iff _ _ _ _).mp hblock
  have hX : X.PosDef := by
    simpa only [add_sub_cancel] using hQ.add_posSemidef hdiff
  have hdetQ : Q.det = ∏ i, Z i i := by
    simp only [Q, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv,
      D, Matrix.det_diagonal, hdetZ, Ring.inverse_eq_inv]
    field_simp
  exact ⟨hX, hdetQ ▸ det_le_det hQ hdiff⟩

/-- The positive-definite log-determinant hypograph has an exact PSD/exponential
lift. The public rule requires positive dimension; the function itself remains
the ordinary totalized logarithm of the determinant. -/
theorem hypograph_iff (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (_hn : 0 < n) :
    (X.PosDef ∧ t ≤ Fn.logDet X) ↔
      ∃ z : LowerTriangularEntries n, ∃ u : Fin n → ℝ,
        (fromBlocksFin X (lowerTriangularMatrix z) (lowerTriangularMatrix z).transpose
          (Matrix.diagonal (fun i => lowerTriangularMatrix z i i))).PosSemidef ∧
        (∀ i, (u i, 1, lowerTriangularMatrix z i i) ∈ EXP) ∧ t ≤ ∑ i, u i := by
  constructor
  · rintro ⟨hX, ht⟩
    obtain ⟨Z, hZ, hd, hblock, hdet⟩ := exists_triangular_block hX
    let z : LowerTriangularEntries n := fun ij => Z ij.1.1 ij.1.2
    have hz : lowerTriangularMatrix z = Z := lowerTriangularMatrix_restrict Z hZ
    refine ⟨z, fun i => Real.log (Z i i), ?_, ?_, ?_⟩
    · simpa only [hz] using hblock
    · intro i
      rw [hz]
      exact (Exponential.le_log_iff _ _ (hd i)).mp le_rfl
    · change t ≤ Real.log X.det at ht
      rwa [hdet, Real.log_prod (fun i _ => (hd i).ne')] at ht
  · rintro ⟨z, u, hblock, hu, ht⟩
    have hd : ∀ i, 0 < lowerTriangularMatrix z i i := fun i =>
      (Real.exp_pos (u i)).trans_le ((Exponential.exp_le_iff _ _).mpr (hu i))
    obtain ⟨hX, hdet⟩ := posDef_and_prod_le_det_of_triangular_block
      (lowerTriangularMatrix_isLowerTriangular z) hd hblock
    refine ⟨hX, ht.trans ?_⟩
    calc
      ∑ i, u i ≤ ∑ i, Real.log (lowerTriangularMatrix z i i) :=
        Finset.sum_le_sum fun i _ => (Exponential.le_log_iff _ _ (hd i)).mpr (hu i)
      _ = Real.log (∏ i, lowerTriangularMatrix z i i) :=
        (Real.log_prod (fun i _ => (hd i).ne')).symm
      _ ≤ Fn.logDet X := Real.log_le_log (Finset.prod_pos fun i _ => hd i) hdet

/-- The same lift as a hypograph representation on the established matrix domain. -/
theorem le_logDet_iff (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosDef)
    (t : ℝ) (hn : 0 < n) :
    t ≤ Fn.logDet X ↔
      ∃ z : LowerTriangularEntries n, ∃ u : Fin n → ℝ,
        (fromBlocksFin X (lowerTriangularMatrix z) (lowerTriangularMatrix z).transpose
          (Matrix.diagonal (fun i => lowerTriangularMatrix z i i))).PosSemidef ∧
        (∀ i, (u i, 1, lowerTriangularMatrix z i i) ∈ EXP) ∧ t ≤ ∑ i, u i := by
  simpa only [hX, true_and] using hypograph_iff X t hn

end Morew.Conic.LogDet
