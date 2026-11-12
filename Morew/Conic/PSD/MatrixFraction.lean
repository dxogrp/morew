/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Fn.Matrix
import Morew.Conic.PSD

/-!
# Matrix-fractional epigraph

On the positive-definite domain, a Schur complement gives a semidefinite
representation of the matrix-fractional epigraph.
-/

namespace Morew.Conic.MatrixFraction

open Matrix

/-- A matrix-fractional upper bound is equivalent to a semidefinite block constraint. -/
theorem matFrac_le_iff {n : Nat} (x : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (t : ℝ) :
    Fn.matFrac x P ≤ t ↔
      (fromBlocksFin P (fun (i : Fin n) (_ : Fin 1) => x i) (fun _ : Fin 1 => x)
        (Matrix.diagonal (fun _ : Fin 1 => t))).PosSemidef := by
  let A := SymmetricMatrix.ofMatrix P (Matrix.isHermitian_iff_isSymm.mp hP.isHermitian)
  let D := SymmetricMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin 1 => t))
    (Matrix.isSymm_diagonal _)
  let B : Matrix (Fin n) (Fin 1) ℝ := fun i _ => x i
  have hscalar : D.toMatrix - B.transpose * A.toMatrix⁻¹ * B =
      Matrix.diagonal (fun _ : Fin 1 => t - Fn.matFrac x P) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    change t - ∑ k, (∑ l, x l * P⁻¹ l k) * x k =
      t - ∑ l, x l * ∑ k, P⁻¹ l k * x k
    congr 1
    exact (Matrix.dotProduct_mulVec x P⁻¹ x).symm
  have hs := schurComplement_mem_iff A B D hP
  rw [hscalar] at hs
  have hB : B.transpose = (fun _ : Fin 1 => x) := by ext i j; rfl
  simpa [A, D, SymmetricMatrix.fromBlocks, hB, B, sub_nonneg] using hs

end Morew.Conic.MatrixFraction
