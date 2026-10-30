/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD
import Mathlib.Analysis.Matrix.Order

/-!
# An exact positive-definite domain lift

A symmetric inverse witness turns positive definiteness into an existential
PSD block with identity off-diagonal blocks. The reverse implication uses the
kernel of a PSD quadratic form, so no strict spectral margin is introduced.
-/

namespace Morew.Conic

open Matrix

/-- A PSD block with identity off-diagonal blocks has a positive-definite
upper-left corner. No symmetry premise on either input is needed. -/
theorem posDef_of_fromBlocksFin_identity_posSemidef {n : Nat}
    (P W : Matrix (Fin n) (Fin n) ℝ)
    (h : (fromBlocksFin P 1 1 W).PosSemidef) : P.PosDef := by
  have hB := (posSemidef_fromBlocksFin_iff P 1 1 W).mp h
  have hP : P.PosSemidef := by
    have he : (Matrix.fromBlocks P 1 1 W).submatrix Sum.inl Sum.inl = P := by
      ext i j
      rfl
    simpa only [he] using hB.submatrix Sum.inl
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hP.isHermitian
  intro x hx
  have hnonneg := hP.dotProduct_mulVec_nonneg x
  refine lt_of_le_of_ne hnonneg ?_
  intro heq
  have hzero : star (Sum.elim x (0 : Fin n → ℝ)) ⬝ᵥ
      (Matrix.fromBlocks P 1 1 W *ᵥ Sum.elim x 0) = 0 := by
    simpa [Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim,
      Function.star_sumElim] using heq.symm
  have hkernel := hB.dotProduct_mulVec_zero_iff (Sum.elim x (0 : Fin n → ℝ)) |>.mp hzero
  apply hx
  funext i
  simpa [Matrix.fromBlocks_mulVec] using congrFun hkernel (Sum.inr i)

/-- Positive definiteness is exactly the existence of a symmetric inverse
witness in an identity-coupled PSD block, including dimension zero. -/
theorem posDef_iff_exists_identity_block {n : Nat}
    (P : Matrix (Fin n) (Fin n) ℝ) :
    P.PosDef ↔ ∃ W : SymmetricMatrix n, (fromBlocksFin P 1 1 W.toMatrix).PosSemidef := by
  constructor
  · intro hP
    let A := SymmetricMatrix.ofMatrix P (Matrix.isHermitian_iff_isSymm.mp hP.isHermitian)
    let W := SymmetricMatrix.ofMatrix P⁻¹
      (Matrix.isHermitian_iff_isSymm.mp hP.isHermitian).inv
    refine ⟨W, ?_⟩
    have h := (schurComplement_mem_iff A (1 : Matrix (Fin n) (Fin n) ℝ) W hP).mp
      (by simpa [A, W] using (Matrix.PosSemidef.zero (n := Fin n) (R := ℝ)))
    simpa [A, W, SymmetricMatrix.fromBlocks] using h
  · rintro ⟨W, hW⟩
    exact posDef_of_fromBlocksFin_identity_posSemidef P W.toMatrix hW

end Morew.Conic
