/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Morew.Conic.SecondOrder
public import Morew.Fn.Matrix
public import Morew.Fn.Norm

/-!
# Quadratic-form epigraphs

A positive-semidefinite matrix has a square-root factor determined by the matrix.
Its quadratic form is the squared Euclidean norm of the factored vector, so its
epigraph is a rotated second-order cone constraint. Singular matrices and empty
vectors require no additional assumptions.
-/

@[expose] public section

namespace Morew.Conic.QuadForm

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- The positive-semidefinite square-root factor, independent of any proof about `Q`. -/
noncomputable def factor {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := CFC.sqrt Q

@[simp] theorem factor_zero {n : Nat} :
    factor (0 : Matrix (Fin n) (Fin n) ℝ) = 0 := by
  simp [factor]

/-- A positive-semidefinite matrix is the Gram matrix of its square-root factor. -/
theorem factor_transpose_mul_self {n : Nat} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosSemidef) : (factor Q).transpose * factor Q = Q := by
  have hR : (factor Q).PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  have hRR : factor Q * factor Q = Q := by
    simpa only [factor, pow_two] using CFC.sq_sqrt Q hQ.nonneg
  have hT : (factor Q).transpose = factor Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  rw [hT, hRR]

/-- A matrix quadratic form is a squared Euclidean norm after applying the factor. -/
theorem dotProduct_mulVec_eq_norm2_sq {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) :
    x ⬝ᵥ (Q *ᵥ x) = Fn.norm2 (factor Q *ᵥ x) ^ 2 := by
  conv_lhs => rw [← factor_transpose_mul_self Q hQ]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, Fn.norm2_sq_eq_sum]
  simp only [dotProduct, pow_two]

/-- The named quadratic form has the same squared-norm factorization. -/
theorem quadForm_eq_norm2_sq {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) :
    Fn.quadForm x Q = Fn.norm2 (factor Q *ᵥ x) ^ 2 :=
  dotProduct_mulVec_eq_norm2_sq x Q hQ

/-- A positive-semidefinite quadratic bound is one rotated second-order cone row. -/
theorem quadForm_le_iff {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) (t : ℝ) :
    Fn.quadForm x Q ≤ t ↔
      (t, 1 / 2, factor Q *ᵥ x) ∈ (Cone.rotatedSecondOrder n).carrier := by
  rw [quadForm_eq_norm2_sq x Q hQ]
  exact SecondOrder.norm_toLp_sq_le_iff _ _

/-- The native matrix quadratic bound uses the same rotated cone coordinates. -/
theorem dotProduct_mulVec_le_iff {n : Nat} (x : Fin n → ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosSemidef) (t : ℝ) :
    x ⬝ᵥ (Q *ᵥ x) ≤ t ↔
      (t, 1 / 2, factor Q *ᵥ x) ∈ (Cone.rotatedSecondOrder n).carrier :=
  quadForm_le_iff x Q hQ t

end Morew.Conic.QuadForm
