/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD
import Mathlib.Analysis.Matrix.Order

/-!
# A semidefinite representation of positive definiteness

Positive definiteness is equivalent to the existence of a positive-semidefinite
block completion with identity off-diagonal blocks.
-/

namespace Morew.Conic

open Matrix

/-- A positive-semidefinite block with identity off-diagonal blocks has a
positive-definite upper-left block. -/
theorem posDef_of_fromBlocksFin_identity_psd {n : Nat}
    (P W : Matrix (Fin n) (Fin n) ℝ)
    (h : (fromBlocksFin P 1 1 W).PosSemidef) : P.PosDef := by
  have hB := (psd_fromBlocksFin_iff P 1 1 W).mp h
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

/-- Positive definiteness is equivalent to a semidefinite block completion
with identity off-diagonal blocks. -/
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
    exact posDef_of_fromBlocksFin_identity_psd P W.toMatrix hW

end Morew.Conic
