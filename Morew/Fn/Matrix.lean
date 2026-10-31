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

The largest eigenvalue uses the supremum of the real spectrum. Its exact
semidefinite representation requires a symmetric matrix of positive dimension;
the empty spectrum has supremum zero in `ℝ`.

The matrix fraction uses the totalized native inverse. Its exact Schur
representation separately requires positive definiteness and does not extend
its domain to singular matrices.

The nuclear norm is the sum of the singular values of the associated Euclidean
linear map. The domain dimension bounds the support, including empty matrices.

The log determinant uses the totalized real logarithm. Its exact conic
representation separately requires positive definiteness.
-/

namespace Morew.Fn

open Matrix

/-- The logarithm of the determinant, with its usual domain requiring `X.PosDef`. -/
noncomputable def logDet {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log X.det

@[simp] theorem logDet_empty (X : Matrix (Fin 0) (Fin 0) ℝ) : logDet X = 0 := by
  simp [logDet]

/-- The supremum of the real spectrum; on nonempty symmetric matrices this is
the largest eigenvalue. -/
noncomputable def lambdaMax {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

/-- The real matrix fraction, with its usual domain requiring `P.PosDef`. -/
noncomputable def matrixFrac {n : Nat} (x : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : ℝ := x ⬝ᵥ (P⁻¹ *ᵥ x)

/-- The matrix fraction on an empty vector is zero. -/
@[simp] theorem matrixFrac_empty (x : Fin 0 → ℝ) (P : Matrix (Fin 0) (Fin 0) ℝ) :
    matrixFrac x P = 0 := by simp [matrixFrac, dotProduct]

/-- The sum of the singular values, with their multiplicities. -/
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
