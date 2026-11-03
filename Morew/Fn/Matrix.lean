/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Real matrix modeling functions

Largest eigenvalues, matrix fractions, nuclear norms, and log-determinants
are real-valued functions on ordinary matrices. Their exact conic
representations use the domains stated at each definition.
-/

namespace Morew.Fn

open Matrix

/-- The total real function `Real.log X.det`. Its conic representation requires
`X.PosDef`. The value on an empty matrix is zero. -/
noncomputable def logDet {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log X.det

@[simp] theorem logDet_empty (X : Matrix (Fin 0) (Fin 0) ℝ) : logDet X = 0 := by
  simp [logDet]

/-- The supremum of the real spectrum; on nonempty symmetric matrices this is
the largest eigenvalue and has an exact semidefinite representation. The
supremum of the empty spectrum is zero in `ℝ`. -/
noncomputable def lambdaMax {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

/-- The real matrix fraction using mathlib's total matrix inverse. Its exact
Schur-complement representation requires `P.PosDef`. -/
noncomputable def matrixFrac {n : Nat} (x : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : ℝ := x ⬝ᵥ (P⁻¹ *ᵥ x)

/-- The matrix fraction on an empty vector is zero. -/
@[simp] theorem matrixFrac_empty (x : Fin 0 → ℝ) (P : Matrix (Fin 0) (Fin 0) ℝ) :
    matrixFrac x P = 0 := by simp [matrixFrac, dotProduct]

/-- The sum of the singular values, with multiplicity, of the associated Euclidean
linear map, indexed by the domain dimension. The value is zero if either dimension is empty. -/
noncomputable def nuclearNorm {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, (Matrix.toEuclideanLin A).singularValues i

theorem nuclearNorm_nonneg {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ nuclearNorm A :=
  Finset.sum_nonneg fun i _ => (Matrix.toEuclideanLin A).singularValues_nonneg i

@[simp] theorem nuclearNorm_zero {m n : Nat} :
    nuclearNorm (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  simp [nuclearNorm]

@[simp] theorem nuclearNorm_empty_columns {m : Nat} (A : Matrix (Fin m) (Fin 0) ℝ) :
    nuclearNorm A = 0 := by
  simp [nuclearNorm]

@[simp] theorem nuclearNorm_empty_rows {n : Nat} (A : Matrix (Fin 0) (Fin n) ℝ) :
    nuclearNorm A = 0 := by
  have : A = 0 := Subsingleton.elim _ _
  simp [this]

end Morew.Fn
