/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Real matrix modeling functions

Quadratic forms, extreme eigenvalues, matrix-fractional functions, nuclear norms, and
log-determinants. The conic representations use the domains stated below.
-/

namespace Morew.Fn

open Matrix

/-- The quadratic form `xᵀ Q x`, with no factor of one half.
The matrix may be arbitrary; a positive semidefinite matrix gives a nonnegative value. -/
noncomputable def quadForm {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ := x ⬝ᵥ (Q *ᵥ x)

/-- The named quadratic form agrees with the native matrix expression. -/
theorem quadForm_eq_dotProduct_mulVec {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : quadForm x Q = x ⬝ᵥ (Q *ᵥ x) := rfl

/-- The named quadratic form uses Mathlib's matrix quadratic form convention. -/
theorem quadForm_eq_toQuadraticForm {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) : quadForm x Q = Q.toQuadraticForm' x := by
  simp [quadForm, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

/-- Positive semidefiniteness makes the quadratic form nonnegative. -/
theorem quadForm_nonneg {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) : 0 ≤ quadForm x Q :=
  hQ.dotProduct_mulVec_nonneg x

@[simp] theorem quadForm_zero_vector {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ) :
    quadForm 0 Q = 0 := by simp [quadForm]

@[simp] theorem quadForm_zero_matrix {n : Nat} (x : Fin n → ℝ) :
    quadForm x 0 = 0 := by simp [quadForm]

/-- The quadratic form on an empty vector is zero. -/
@[simp] theorem quadForm_empty (x : Fin 0 → ℝ) (Q : Matrix (Fin 0) (Fin 0) ℝ) :
    quadForm x Q = 0 := by simp [quadForm, dotProduct]

/-- The log-determinant `Real.log X.det`, using the total real logarithm.
Its conic representation requires `X.PosDef`. -/
noncomputable def logDet {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.log X.det

@[simp] theorem logDet_empty (X : Matrix (Fin 0) (Fin 0) ℝ) : logDet X = 0 := by
  simp [logDet]

/-- The supremum of the real spectrum, equal to the largest eigenvalue for a
symmetric matrix of positive dimension. The empty spectrum has supremum zero. -/
noncomputable def lambdaMax {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (spectrum ℝ A)

/-- The infimum of the real spectrum, equal to the smallest eigenvalue for a
symmetric matrix of positive dimension. The empty spectrum has infimum zero. -/
noncomputable def lambdaMin {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf (spectrum ℝ A)

/-- The smallest spectral value is the negative of the largest value of the negated matrix. -/
theorem lambdaMin_eq_neg_lambdaMax {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) :
    lambdaMin A = -lambdaMax (-A) := by
  rw [lambdaMin, lambdaMax, ← spectrum.neg_eq, Real.sSup_neg, neg_neg]

@[simp] theorem lambdaMin_empty (A : Matrix (Fin 0) (Fin 0) ℝ) : lambdaMin A = 0 := by
  simp only [lambdaMin, spectrum.of_subsingleton, Real.sInf_empty]

/-- The matrix-fractional function `xᵀ P⁻¹ x`, using mathlib's total inverse.
Its Schur-complement representation requires `P.PosDef`. -/
noncomputable def matFrac {n : Nat} (x : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : ℝ := x ⬝ᵥ (P⁻¹ *ᵥ x)

/-- The matrix fraction on an empty vector is zero. -/
@[simp] theorem matFrac_empty (x : Fin 0 → ℝ) (P : Matrix (Fin 0) (Fin 0) ℝ) :
    matFrac x P = 0 := by simp [matFrac, dotProduct]

/-- The sum of the singular values, counted with multiplicity. -/
noncomputable def normNuc {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, (Matrix.toEuclideanLin A).singularValues i

theorem normNuc_nonneg {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ normNuc A :=
  Finset.sum_nonneg fun i _ => (Matrix.toEuclideanLin A).singularValues_nonneg i

@[simp] theorem normNuc_zero {m n : Nat} :
    normNuc (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  simp [normNuc]

@[simp] theorem normNuc_empty_columns {m : Nat} (A : Matrix (Fin m) (Fin 0) ℝ) :
    normNuc A = 0 := by
  simp [normNuc]

@[simp] theorem normNuc_empty_rows {n : Nat} (A : Matrix (Fin 0) (Fin n) ℝ) :
    normNuc A = 0 := by
  have : A = 0 := Subsingleton.elim _ _
  simp [this]

end Morew.Fn
