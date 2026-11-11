/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Cone
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Symmetric matrices and positive-semidefinite cones

Real symmetric matrices inherit the entrywise supremum norm. Schur-complement
identities use positive-definite pivots; block matrices are indexed by
`Fin (m + n)`.

`Morew.Conic.PSD.Repr` provides rewrite records for spectral bounds,
matrix-fractional functions, log-determinants, and positive definiteness.
-/

namespace Morew.Conic

/-- The submodule of symmetric real matrices. -/
def symmetricMatrixSubmodule (n : Nat) : Submodule ℝ (Fin n → Fin n → ℝ) where
  carrier := {M | Matrix.IsSymm M}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := Matrix.IsSymm.add
  smul_mem' c _ h := h.smul c

/-- Symmetric real `n × n` matrices. -/
abbrev SymmetricMatrix (n : Nat) : Type := ↥(symmetricMatrixSubmodule n)

namespace SymmetricMatrix

/-- Construct a `SymmetricMatrix` from a real matrix and a symmetry proof. -/
def ofMatrix {n : Nat} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    SymmetricMatrix n := ⟨M, hM⟩

/-- The underlying real matrix. -/
def toMatrix {n : Nat} (M : SymmetricMatrix n) : Matrix (Fin n) (Fin n) ℝ := M.val

/-- The underlying matrix is symmetric. -/
theorem toMatrix_isSymm {n : Nat} (M : SymmetricMatrix n) : M.toMatrix.IsSymm :=
  M.property

/-- Conversion to `SymmetricMatrix` preserves the underlying matrix. -/
@[simp]
theorem toMatrix_ofMatrix {n : Nat} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (ofMatrix M hM).toMatrix = M := rfl

/-- Reconstructing a `SymmetricMatrix` from its entries recovers the original. -/
@[simp]
theorem ofMatrix_toMatrix {n : Nat} (M : SymmetricMatrix n) :
    ofMatrix M.toMatrix M.toMatrix_isSymm = M := rfl

/-- The underlying matrix determines the symmetric matrix. -/
theorem toMatrix_injective {n : Nat} :
    Function.Injective (toMatrix : SymmetricMatrix n → Matrix (Fin n) (Fin n) ℝ) :=
  Subtype.coe_injective

/-- Symmetric matrices are equal when their entries agree. -/
@[ext]
theorem ext {n : Nat} {M N : SymmetricMatrix n}
    (h : ∀ i j, M.toMatrix i j = N.toMatrix i j) : M = N :=
  toMatrix_injective (Matrix.ext h)

@[simp]
theorem toMatrix_zero {n : Nat} : (0 : SymmetricMatrix n).toMatrix = 0 := rfl

@[simp]
theorem toMatrix_add {n : Nat} (M N : SymmetricMatrix n) :
    (M + N).toMatrix = M.toMatrix + N.toMatrix := rfl

@[simp]
theorem toMatrix_neg {n : Nat} (M : SymmetricMatrix n) :
    (-M).toMatrix = -M.toMatrix := rfl

@[simp]
theorem toMatrix_sub {n : Nat} (M N : SymmetricMatrix n) :
    (M - N).toMatrix = M.toMatrix - N.toMatrix := rfl

@[simp]
theorem toMatrix_smul {n : Nat} (c : ℝ) (M : SymmetricMatrix n) :
    (c • M).toMatrix = c • M.toMatrix := rfl

/-- Forgetting the symmetry proof is a real linear map. -/
def toMatrixLinearMap (n : Nat) :
    SymmetricMatrix n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := toMatrix
  map_add' := toMatrix_add
  map_smul' := toMatrix_smul

@[simp]
theorem toMatrixLinearMap_apply {n : Nat} (M : SymmetricMatrix n) :
    toMatrixLinearMap n M = M.toMatrix := rfl

end SymmetricMatrix

namespace Cone

/-- The positive-semidefinite cone in the real symmetric-matrix space. -/
noncomputable def psd (n : Nat) : Cone where
  Space := SymmetricMatrix n
  carrier := {
    carrier := {M | M.toMatrix.PosSemidef}
    smul_mem' := by
      intro c hc M hM
      exact hM.smul hc.le
    add_mem' := by
      intro M hM N hN
      exact hM.add hN }

/-- Cone membership is equivalent to positive semidefiniteness. -/
@[simp]
theorem mem_psd {n : Nat} (M : SymmetricMatrix n) :
    M ∈ (psd n).carrier ↔ M.toMatrix.PosSemidef := Iff.rfl

end Cone

set_option quotPrecheck false in
/-- The positive-semidefinite cone of symmetric `n × n` matrices. -/
notation:max (name := psdCarrier) "PSD " n:arg =>
  (Morew.Conic.Cone.psd n).carrier

section Blocks

variable {m n : Nat}

/-- An ordinary block matrix indexed by the first `m` and last `n` elements of
`Fin (m + n)`. -/
def fromBlocksFin
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (m + n)) (Fin (m + n)) ℝ :=
  (Matrix.fromBlocks A B C D).reindex finSumFinEquiv finSumFinEquiv

variable (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
  (C : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin n) (Fin n) ℝ)

@[simp]
theorem fromBlocksFin_apply₁₁ (i j : Fin m) :
    fromBlocksFin A B C D (Fin.castAdd n i) (Fin.castAdd n j) = A i j := by
  simp [fromBlocksFin, Matrix.reindex_apply]

@[simp]
theorem fromBlocksFin_apply₁₂ (i : Fin m) (j : Fin n) :
    fromBlocksFin A B C D (Fin.castAdd n i) (Fin.natAdd m j) = B i j := by
  simp [fromBlocksFin, Matrix.reindex_apply]

@[simp]
theorem fromBlocksFin_apply₂₁ (i : Fin n) (j : Fin m) :
    fromBlocksFin A B C D (Fin.natAdd m i) (Fin.castAdd n j) = C i j := by
  simp [fromBlocksFin, Matrix.reindex_apply]

@[simp]
theorem fromBlocksFin_apply₂₂ (i j : Fin n) :
    fromBlocksFin A B C D (Fin.natAdd m i) (Fin.natAdd m j) = D i j := by
  simp [fromBlocksFin, Matrix.reindex_apply]

/-- Block reindexing preserves positive semidefiniteness. -/
theorem psd_fromBlocksFin_iff :
    (fromBlocksFin A B C D).PosSemidef ↔
      (Matrix.fromBlocks A B C D).PosSemidef :=
  Matrix.posSemidef_submatrix_equiv finSumFinEquiv.symm

/-- Block reindexing preserves symmetry. -/
theorem isSymm_fromBlocksFin (hA : A.IsSymm) (hBC : B.transpose = C) (hD : D.IsSymm) :
    (fromBlocksFin A B C D).IsSymm :=
  (hA.fromBlocks hBC hD).reindex finSumFinEquiv

end Blocks

namespace SymmetricMatrix

/-- The symmetric block matrix `[A B; Bᵀ D]`, indexed by `Fin (m + n)`. -/
def fromBlocks {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) : SymmetricMatrix (m + n) :=
  ofMatrix (fromBlocksFin A.toMatrix B B.transpose D.toMatrix)
    (isSymm_fromBlocksFin _ _ _ _ A.toMatrix_isSymm rfl D.toMatrix_isSymm)

@[simp]
theorem toMatrix_fromBlocks {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) :
    (fromBlocks A B D).toMatrix = fromBlocksFin A.toMatrix B B.transpose D.toMatrix := rfl

end SymmetricMatrix

/-- With a positive-definite upper-left block, the block matrix is positive
semidefinite if and only if its Schur complement is positive semidefinite. -/
theorem schurComplement_mem_iff {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n)
    (hA : A.toMatrix.PosDef) :
    (D.toMatrix - B.transpose * A.toMatrix⁻¹ * B).PosSemidef ↔
      SymmetricMatrix.fromBlocks A B D ∈ PSD (m + n) := by
  let := hA.isUnit.invertible
  rw [Cone.mem_psd, SymmetricMatrix.toMatrix_fromBlocks,
    psd_fromBlocksFin_iff]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosDef.fromBlocks₁₁ B D.toMatrix hA).symm

/-- With a positive-definite lower-right block, the block matrix is positive
semidefinite if and only if its Schur complement is positive semidefinite. -/
theorem schurComplement_mem_iff_right {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n)
    (hD : D.toMatrix.PosDef) :
    (A.toMatrix - B * D.toMatrix⁻¹ * B.transpose).PosSemidef ↔
      SymmetricMatrix.fromBlocks A B D ∈ PSD (m + n) := by
  let := hD.isUnit.invertible
  rw [Cone.mem_psd, SymmetricMatrix.toMatrix_fromBlocks,
    psd_fromBlocksFin_iff]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosDef.fromBlocks₂₂ A.toMatrix B hD).symm

end Morew.Conic
