/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.Triangular

/-! Exact lower-triangular coordinates, including symbolic and empty dimensions. -/

namespace MorewTest.Conic.Triangular

open Morew.Conic

variable {n : Nat}

example (z : LowerTriangularEntries n) (i j : Fin n) (h : j ≤ i) :
    lowerTriangularMatrix z i j = z ⟨(i, j), h⟩ :=
  lowerTriangularMatrix_apply_of_le z h

example (z : LowerTriangularEntries n) (i j : Fin n) (h : i < j) :
    lowerTriangularMatrix z i j = 0 := lowerTriangularMatrix_apply_of_lt z h

example (z : LowerTriangularEntries n) :
    (lowerTriangularMatrix z).IsLowerTriangular := lowerTriangularMatrix_isLowerTriangular z

example (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsLowerTriangular) :
    lowerTriangularMatrix (fun ij => A ij.1.1 ij.1.2) = A :=
  lowerTriangularMatrix_restrict A hA

example (z w : LowerTriangularEntries n) :
    lowerTriangularMatrix (z + w) = lowerTriangularMatrix z + lowerTriangularMatrix w :=
  (lowerTriangularMatrixLinearMap n).map_add z w

example (c : ℝ) (z : LowerTriangularEntries n) :
    lowerTriangularMatrix (c • z) = c • lowerTriangularMatrix z :=
  (lowerTriangularMatrixLinearMap n).map_smul c z

example (z : LowerTriangularEntries 0) : lowerTriangularMatrix z = 0 := by
  ext i
  exact Fin.elim0 i

example (z : LowerTriangularEntries 1) :
    lowerTriangularMatrix z 0 0 = z ⟨(0, 0), le_rfl⟩ := by simp

example (z : LowerTriangularEntries 2) :
    lowerTriangularMatrix z 0 1 = 0 := by
  exact lowerTriangularMatrix_apply_of_lt z (by decide)

end MorewTest.Conic.Triangular
