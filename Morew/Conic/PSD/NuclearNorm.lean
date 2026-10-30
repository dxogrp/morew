/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.SingularVectors
import Morew.Conic.PSD

/-!
# Exact semidefinite representation of the nuclear norm

The auxiliary symmetric matrices use the standard half-trace normalization.
Singular-vector witnesses attain the norm, including zero and empty matrices.
-/

namespace Morew.Conic.Spectral

open Matrix
open scoped RealInnerProductSpace

private theorem trace_outer {n : Nat} (v : EuclideanSpace ℝ (Fin n)) :
    (Matrix.vecMulVec v.ofLp v.ofLp).trace = ‖v‖ ^ 2 := by
  rw [Matrix.trace_vecMulVec]
  change ⟪v, v⟫ = _
  exact real_inner_self_eq_norm_sq v

private theorem quadratic_outer {n : Nat} (v u : EuclideanSpace ℝ (Fin n)) :
    u.ofLp ⬝ᵥ Matrix.vecMulVec v.ofLp v.ofLp *ᵥ u.ofLp = ⟪v, u⟫ ^ 2 := by
  simp [Matrix.vecMulVec_mulVec, dotProduct_smul, EuclideanSpace.inner_eq_star_dotProduct,
    smul_eq_mul, pow_two, dotProduct_comm]

/-- A positive quadratic form summed over an orthonormal family is bounded by
its trace. Completeness of the family is unnecessary. -/
theorem sum_quadratic_le_trace {n : Nat} {ι : Type*} [Fintype ι]
    {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.PosSemidef)
    (u : ι → EuclideanSpace ℝ (Fin n)) (hu : Orthonormal ℝ u) :
    (∑ i, (u i).ofLp ⬝ᵥ W *ᵥ (u i).ofLp) ≤ W.trace := by
  classical
  obtain ⟨k, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hW
  simp only [star_trivial, Matrix.sum_mulVec, dotProduct_sum, Matrix.trace_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (v j)
  change (∑ i, (u i).ofLp ⬝ᵥ Matrix.vecMulVec w.ofLp w.ofLp *ᵥ (u i).ofLp) ≤ _
  simp_rw [quadratic_outer]
  rw [show v j = w.ofLp from rfl, trace_outer]
  simpa only [Real.norm_eq_abs, sq_abs, real_inner_comm] using
    (hu.sum_inner_products_le (s := Finset.univ) w)

variable {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ)

/-- The attaining left symmetric matrix in the nuclear-norm lift. -/
noncomputable def nuclearLeftWitness : SymmetricMatrix m :=
  SymmetricMatrix.ofMatrix
    (∑ i : PositiveSingularIndex A, singularValue A i.val •
      Matrix.vecMulVec (leftSingularVector A i).ofLp (leftSingularVector A i).ofLp)
    (by
      apply Matrix.IsSymm.ext
      intro i j
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm])

/-- The attaining right symmetric matrix in the nuclear-norm lift. -/
noncomputable def nuclearRightWitness : SymmetricMatrix n :=
  SymmetricMatrix.ofMatrix
    (∑ i : PositiveSingularIndex A, singularValue A i.val •
      Matrix.vecMulVec (rightSingularBasis A i.val).ofLp (rightSingularBasis A i.val).ofLp)
    (by
      apply Matrix.IsSymm.ext
      intro i j
      simp [Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm])

theorem trace_nuclearLeftWitness : (nuclearLeftWitness A).toMatrix.trace = Fn.nuclearNorm A := by
  classical
  change (∑ i : PositiveSingularIndex A, singularValue A i.val •
    Matrix.vecMulVec (leftSingularVector A i).ofLp (leftSingularVector A i).ofLp).trace = _
  simp only [Matrix.trace_sum, Matrix.trace_smul, trace_outer,
    (leftSingularVector_orthonormal A).norm_eq_one, one_pow, smul_eq_mul, mul_one]
  exact sum_positive_singularValues A

theorem trace_nuclearRightWitness : (nuclearRightWitness A).toMatrix.trace = Fn.nuclearNorm A := by
  classical
  change (∑ i : PositiveSingularIndex A, singularValue A i.val •
    Matrix.vecMulVec (rightSingularBasis A i.val).ofLp
      (rightSingularBasis A i.val).ofLp).trace = _
  simp only [Matrix.trace_sum, Matrix.trace_smul, trace_outer,
    (rightSingularBasis A).orthonormal.norm_eq_one, one_pow, smul_eq_mul, mul_one]
  exact sum_positive_singularValues A

theorem nuclearWitness_block_posSemidef :
    (Matrix.fromBlocks (nuclearLeftWitness A).toMatrix A A.transpose
      (nuclearRightWitness A).toMatrix).PosSemidef := by
  classical
  let w (i : PositiveSingularIndex A) : Fin m ⊕ Fin n → ℝ :=
    Sum.elim (leftSingularVector A i).ofLp (rightSingularBasis A i.val).ofLp
  have heq : Matrix.fromBlocks (nuclearLeftWitness A).toMatrix A A.transpose
      (nuclearRightWitness A).toMatrix =
      ∑ i : PositiveSingularIndex A, singularValue A i.val • Matrix.vecMulVec (w i) (w i) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [nuclearLeftWitness, w, Matrix.sum_apply, Matrix.vecMulVec_apply]
      | inr j =>
        simpa [w, Matrix.sum_apply, Matrix.vecMulVec_apply] using
          congrArg (fun M : Matrix (Fin m) (Fin n) ℝ => M i j) (matrix_eq_sum_positive A)
    | inr i =>
      cases j with
      | inl j =>
        simpa [w, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm] using
          congrArg (fun M : Matrix (Fin m) (Fin n) ℝ => M j i) (matrix_eq_sum_positive A)
      | inr j => simp [nuclearRightWitness, w, Matrix.sum_apply, Matrix.vecMulVec_apply]
  rw [heq]
  apply Matrix.posSemidef_sum
  intro i _
  have hw : (Matrix.vecMulVec (w i) (w i)).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (w i)
  exact hw.smul (singularValue_nonneg A i.val)

private theorem singular_cross (i : PositiveSingularIndex A) :
    (leftSingularVector A i).ofLp ⬝ᵥ A *ᵥ (rightSingularBasis A i.val).ofLp =
      singularValue A i.val := by
  rw [dotProduct_comm]
  change ⟪leftSingularVector A i,
    Matrix.toEuclideanLin A (rightSingularBasis A i.val)⟫ = _
  rw [← singularValue_smul_leftSingularVector A i, inner_smul_right,
    real_inner_self_eq_norm_sq, (leftSingularVector_orthonormal A).norm_eq_one]
  ring

/-- Every positive-semidefinite block completion bounds the nuclear norm by
half the sum of its diagonal-block traces. -/
theorem nuclearNorm_le_half_trace {W : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ}
    (hB : (Matrix.fromBlocks W A A.transpose V).PosSemidef) :
    Fn.nuclearNorm A ≤ (W.trace + V.trace) / 2 := by
  classical
  have hW : W.PosSemidef := by
    convert hB.submatrix Sum.inl using 1
    ext i j
    rfl
  have hV : V.PosSemidef := by
    convert hB.submatrix Sum.inr using 1
    ext i j
    rfl
  have hi (i : PositiveSingularIndex A) : 2 * singularValue A i.val ≤
      (leftSingularVector A i).ofLp ⬝ᵥ W *ᵥ (leftSingularVector A i).ofLp +
      (rightSingularBasis A i.val).ofLp ⬝ᵥ V *ᵥ (rightSingularBasis A i.val).ofLp := by
    let u := (leftSingularVector A i).ofLp
    let v := (rightSingularBasis A i.val).ofLp
    have h := hB.dotProduct_mulVec_nonneg (Sum.elim u (-v))
    have hcross : v ⬝ᵥ A.transpose *ᵥ u = u ⬝ᵥ A *ᵥ v := by
      rw [dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    simp only [star_trivial, Matrix.fromBlocks_mulVec, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, Matrix.mulVec_neg, sumElim_dotProduct_sumElim,
      dotProduct_add, dotProduct_neg, neg_dotProduct, neg_neg] at h
    rw [hcross] at h
    have hc : u ⬝ᵥ A *ᵥ v = singularValue A i.val := singular_cross A i
    change 2 * singularValue A i.val ≤ u ⬝ᵥ W *ᵥ u + v ⬝ᵥ V *ᵥ v
    linarith
  have hsum := Finset.sum_le_sum (fun (i : PositiveSingularIndex A) (_ : i ∈ Finset.univ) => hi i)
  rw [← Finset.mul_sum, sum_positive_singularValues, Finset.sum_add_distrib] at hsum
  have hl := sum_quadratic_le_trace hW (leftSingularVector A) (leftSingularVector_orthonormal A)
  have hr := sum_quadratic_le_trace hV (fun i : PositiveSingularIndex A =>
    rightSingularBasis A i.val) (rightSingularVector_orthonormal A)
  linarith

/-- The exact nuclear-norm epigraph uses two symmetric witnesses and the
standard half-trace inequality. -/
theorem nuclearNorm_le_iff (t : ℝ) :
    Fn.nuclearNorm A ≤ t ↔ ∃ W : SymmetricMatrix m, ∃ V : SymmetricMatrix n,
      SymmetricMatrix.fromBlocks W A V ∈ PSD (m + n) ∧
        (W.toMatrix.trace + V.toMatrix.trace) / 2 ≤ t := by
  constructor
  · intro h
    refine ⟨nuclearLeftWitness A, nuclearRightWitness A, ?_, ?_⟩
    · rw [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
        posSemidef_fromBlocksFin_iff]
      exact nuclearWitness_block_posSemidef A
    · rw [trace_nuclearLeftWitness, trace_nuclearRightWitness]
      linarith
  · rintro ⟨W, V, hB, ht⟩
    rw [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
      posSemidef_fromBlocksFin_iff] at hB
    exact (nuclearNorm_le_half_trace A hB).trans ht

end Morew.Conic.Spectral
