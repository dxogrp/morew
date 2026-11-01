/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Cone
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Symmetric matrices and positive-semidefinite cones

The cone space consists of ordinary real symmetric matrices, with their exact
entries and the inherited finite-coordinate supremum norm. Constructing a
symmetric matrix requires a symmetry proof; no entries are packed, rescaled, or
symmetrized.

The Schur-complement certificates use an explicitly positive-definite pivot.
Block matrices use the first `m` and last `n` indices of `Fin (m + n)`.

The `Morew.Conic.PSD.*` modules prove exact representations of spectral bounds,
matrix fractions, log-determinants, and positive-definite domains using this cone.
Their rewrite records are available from `Morew.Conic.PSD.Representations`.
-/

namespace Morew.Conic

/-- Symmetric real matrices form a submodule of the ordinary coordinate space.
Writing the ambient space as a function type selects its existing supremum norm
without introducing a global choice of matrix norm. -/
def symmetricMatrixSubmodule (n : Nat) : Submodule ℝ (Fin n → Fin n → ℝ) where
  carrier := {M | Matrix.IsSymm M}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := Matrix.IsSymm.add
  smul_mem' c _ h := h.smul c

/-- Real symmetric matrices of dimension `n`, retaining all ordinary entries. -/
abbrev SymmetricMatrix (n : Nat) : Type := ↥(symmetricMatrixSubmodule n)

namespace SymmetricMatrix

/-- Construct a symmetric matrix from its unchanged entries and a symmetry proof. -/
def ofMatrix {n : Nat} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    SymmetricMatrix n := ⟨M, hM⟩

/-- The ordinary real matrix underlying a symmetric matrix. -/
def toMatrix {n : Nat} (M : SymmetricMatrix n) : Matrix (Fin n) (Fin n) ℝ := M.val

/-- The underlying matrix is symmetric. -/
theorem toMatrix_isSymm {n : Nat} (M : SymmetricMatrix n) : M.toMatrix.IsSymm :=
  M.property

/-- Symmetry of a bundled matrix, exposed independently of its representation. -/
theorem isSymm {n : Nat} (M : SymmetricMatrix n) : M.toMatrix.IsSymm :=
  M.toMatrix_isSymm

/-- Converting a supplied matrix back to ordinary entries preserves it exactly. -/
@[simp]
theorem toMatrix_ofMatrix {n : Nat} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (ofMatrix M hM).toMatrix = M := rfl

/-- Rebundling the underlying entries preserves the symmetric matrix. -/
@[simp]
theorem ofMatrix_toMatrix {n : Nat} (M : SymmetricMatrix n) :
    ofMatrix M.toMatrix M.toMatrix_isSymm = M := rfl

/-- The ordinary matrix uniquely determines the bundled symmetric matrix. -/
theorem toMatrix_injective {n : Nat} :
    Function.Injective (toMatrix : SymmetricMatrix n → Matrix (Fin n) (Fin n) ℝ) :=
  Subtype.coe_injective

/-- Symmetric matrices are equal when their ordinary entries agree. -/
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
noncomputable def positiveSemidefinite (n : Nat) : Cone where
  Space := SymmetricMatrix n
  carrier := {
    carrier := {M | M.toMatrix.PosSemidef}
    smul_mem' := by
      intro c hc M hM
      exact hM.smul hc.le
    add_mem' := by
      intro M hM N hN
      exact hM.add hN }

/-- Cone membership is exactly positive semidefiniteness of the original matrix. -/
@[simp]
theorem mem_positiveSemidefinite {n : Nat} (M : SymmetricMatrix n) :
    M ∈ (positiveSemidefinite n).carrier ↔ M.toMatrix.PosSemidef := Iff.rfl

end Cone

set_option quotPrecheck false in
/-- The positive-semidefinite cone carrier in symmetric dimension `n`. -/
notation:max (name := psdCarrier) "PSD " n:arg =>
  (Morew.Conic.Cone.positiveSemidefinite n).carrier

section Blocks

variable {m n : Nat}

/-- An ordinary block matrix with the first `m` and last `n` indices of
`Fin (m + n)`. Only the canonical block index equivalence is applied. -/
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

/-- Canonical block indexing preserves positive semidefiniteness exactly. -/
theorem posSemidef_fromBlocksFin_iff :
    (fromBlocksFin A B C D).PosSemidef ↔
      (Matrix.fromBlocks A B C D).PosSemidef :=
  Matrix.posSemidef_submatrix_equiv finSumFinEquiv.symm

/-- A symmetric block matrix remains symmetric after canonical block indexing. -/
theorem isSymm_fromBlocksFin (hA : A.IsSymm) (hBC : B.transpose = C) (hD : D.IsSymm) :
    (fromBlocksFin A B C D).IsSymm :=
  (hA.fromBlocks hBC hD).reindex finSumFinEquiv

end Blocks

namespace SymmetricMatrix

/-- The symmetric block matrix `[A B; Bᵀ D]`, in canonical finite coordinates. -/
def fromBlocks {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) : SymmetricMatrix (m + n) :=
  ofMatrix (fromBlocksFin A.toMatrix B B.transpose D.toMatrix)
    (isSymm_fromBlocksFin _ _ _ _ A.toMatrix_isSymm rfl D.toMatrix_isSymm)

@[simp]
theorem toMatrix_fromBlocks {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n) :
    (fromBlocks A B D).toMatrix = fromBlocksFin A.toMatrix B B.transpose D.toMatrix := rfl

end SymmetricMatrix

/-- With a positive-definite upper-left pivot, a Schur complement is positive
semidefinite exactly when the symmetric block matrix belongs to the PSD cone.
Symmetry of both diagonal blocks is carried by their types. -/
theorem schurComplement_mem_iff {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n)
    (hA : A.toMatrix.PosDef) :
    (D.toMatrix - B.transpose * A.toMatrix⁻¹ * B).PosSemidef ↔
      SymmetricMatrix.fromBlocks A B D ∈ PSD (m + n) := by
  let := hA.isUnit.invertible
  rw [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
    posSemidef_fromBlocksFin_iff]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosDef.fromBlocks₁₁ B D.toMatrix hA).symm

/-- With a positive-definite lower-right pivot, a Schur complement is positive
semidefinite exactly when the symmetric block matrix belongs to the PSD cone.
The upper-right block is `B`, and the lower-left block is its transpose. -/
theorem schurComplement_mem_iff_right {m n : Nat} (A : SymmetricMatrix m)
    (B : Matrix (Fin m) (Fin n) ℝ) (D : SymmetricMatrix n)
    (hD : D.toMatrix.PosDef) :
    (A.toMatrix - B * D.toMatrix⁻¹ * B.transpose).PosSemidef ↔
      SymmetricMatrix.fromBlocks A B D ∈ PSD (m + n) := by
  let := hD.isUnit.invertible
  rw [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
    posSemidef_fromBlocksFin_iff]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.PosDef.fromBlocks₂₂ A.toMatrix B hD).symm

end Morew.Conic
