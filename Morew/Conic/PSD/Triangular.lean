/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Real.Basic

/-!
# Lower-triangular matrix coordinates

The auxiliary coordinates contain exactly the entries on and below the diagonal.
Their matrix embedding is linear, including when the dimension is empty.
-/

namespace Morew.Conic

/-- Independent real coordinates on and below the diagonal of a square matrix. -/
abbrev LowerTriangularEntries (n : Nat) :=
  {ij : Fin n × Fin n // ij.2 ≤ ij.1} → ℝ

/-- Fill the upper triangle with zero, retaining the supplied lower entries. -/
def lowerTriangularMatrix {n : Nat} (z : LowerTriangularEntries n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if h : j ≤ i then z ⟨(i, j), h⟩ else 0

@[simp] theorem lowerTriangularMatrix_apply_of_le {n : Nat}
    (z : LowerTriangularEntries n) {i j : Fin n} (h : j ≤ i) :
    lowerTriangularMatrix z i j = z ⟨(i, j), h⟩ := by
  simp [lowerTriangularMatrix, h]

@[simp] theorem lowerTriangularMatrix_apply_of_lt {n : Nat}
    (z : LowerTriangularEntries n) {i j : Fin n} (h : i < j) :
    lowerTriangularMatrix z i j = 0 := by
  simp [lowerTriangularMatrix, not_le_of_gt h]

@[simp] theorem lowerTriangularMatrix_diag {n : Nat} (z : LowerTriangularEntries n) :
    (lowerTriangularMatrix z).diag = fun i => z ⟨(i, i), le_rfl⟩ := by
  funext i
  exact lowerTriangularMatrix_apply_of_le z le_rfl

theorem lowerTriangularMatrix_isLowerTriangular {n : Nat} (z : LowerTriangularEntries n) :
    (lowerTriangularMatrix z).IsLowerTriangular := by
  intro i j h
  exact lowerTriangularMatrix_apply_of_lt z h

/-- Restricting a lower-triangular matrix to these coordinates loses no entries. -/
theorem lowerTriangularMatrix_restrict {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsLowerTriangular) :
    lowerTriangularMatrix (fun ij => A ij.1.1 ij.1.2) = A := by
  ext i j
  by_cases h : j ≤ i
  · simp [lowerTriangularMatrix, h]
  · rw [lowerTriangularMatrix_apply_of_lt _ (lt_of_not_ge h), hA (lt_of_not_ge h)]

theorem lowerTriangularMatrix_injective {n : Nat} :
    Function.Injective (@lowerTriangularMatrix n) := by
  intro z w h
  funext ij
  simpa only [lowerTriangularMatrix_apply_of_le _ ij.property] using
    congrFun (congrFun h ij.1.1) ij.1.2

/-- The zero-filling operation is linear in the independent coordinates. -/
def lowerTriangularMatrixLinearMap (n : Nat) :
    LowerTriangularEntries n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := lowerTriangularMatrix
  map_add' z w := by
    ext i j
    by_cases h : j ≤ i <;> simp [lowerTriangularMatrix, h]
  map_smul' c z := by
    ext i j
    by_cases h : j ≤ i <;> simp [lowerTriangularMatrix, h]

@[simp] theorem lowerTriangularMatrixLinearMap_apply {n : Nat}
    (z : LowerTriangularEntries n) :
    lowerTriangularMatrixLinearMap n z = lowerTriangularMatrix z := rfl

end Morew.Conic
