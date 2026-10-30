/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Fn.Matrix

/-!
# Thin singular-vector decomposition

Only positive singular values need left singular vectors. This construction
therefore applies to rectangular and rank-deficient matrices without extending
an orthonormal family to a full basis.
-/

namespace Morew.Conic.Spectral

open scoped RealInnerProductSpace
open Matrix

variable {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ)

private noncomputable abbrev lin := Matrix.toEuclideanLin A

private theorem dim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp

/-- Singular values indexed by the domain dimension. -/
noncomputable def singularValue (i : Fin n) : ℝ := (lin A).singularValues i

/-- The right singular basis is an eigenbasis of the Gram operator. -/
noncomputable def rightSingularBasis : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (lin A).isSymmetric_adjoint_comp_self.eigenvectorBasis dim

theorem singularValue_nonneg (i : Fin n) : 0 ≤ singularValue A i :=
  (lin A).singularValues_nonneg i

theorem gram_rightSingularBasis (i : Fin n) :
    ((lin A).adjoint ∘ₗ lin A) (rightSingularBasis A i) =
      singularValue A i ^ 2 • rightSingularBasis A i := by
  rw [singularValue, (lin A).sq_singularValues_fin dim]
  exact (lin A).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis dim i

theorem inner_images_rightSingularBasis (i j : Fin n) :
    ⟪lin A (rightSingularBasis A i), lin A (rightSingularBasis A j)⟫ =
      singularValue A j ^ 2 * (if i = j then 1 else 0) := by
  rw [← LinearMap.adjoint_inner_right]
  change ⟪rightSingularBasis A i,
    ((lin A).adjoint ∘ₗ lin A) (rightSingularBasis A j)⟫ = _
  rw [gram_rightSingularBasis, inner_smul_right]
  congr 1
  exact orthonormal_iff_ite.mp (rightSingularBasis A).orthonormal i j

theorem norm_image_rightSingularBasis (i : Fin n) :
    ‖lin A (rightSingularBasis A i)‖ = singularValue A i := by
  have h := inner_images_rightSingularBasis A i i
  rw [real_inner_self_eq_norm_sq] at h
  simp only [ite_true, mul_one] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (singularValue_nonneg A i)).mp h

/-- Indices of the strictly positive singular values. -/
abbrev PositiveSingularIndex := {i : Fin n // 0 < singularValue A i}

noncomputable instance : Fintype (PositiveSingularIndex A) := Fintype.ofFinite _

/-- Normalized images of the positive right singular vectors. -/
noncomputable def leftSingularVector (i : PositiveSingularIndex A) : EuclideanSpace ℝ (Fin m) :=
  (singularValue A i.val)⁻¹ • lin A (rightSingularBasis A i.val)

theorem leftSingularVector_orthonormal : Orthonormal ℝ (leftSingularVector A) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [leftSingularVector, leftSingularVector, inner_smul_left, inner_smul_right,
    inner_images_rightSingularBasis]
  by_cases h : i = j
  · subst j
    simp only [ite_true, mul_one, conj_trivial]
    field_simp [ne_of_gt i.property]
  · have hij : i.val ≠ j.val := fun h' => h (Subtype.ext h')
    simp [h, hij]

theorem rightSingularVector_orthonormal :
    Orthonormal ℝ (fun i : PositiveSingularIndex A => rightSingularBasis A i.val) :=
  (rightSingularBasis A).orthonormal.comp Subtype.val Subtype.val_injective

theorem singularValue_smul_leftSingularVector (i : PositiveSingularIndex A) :
    singularValue A i.val • leftSingularVector A i = lin A (rightSingularBasis A i.val) := by
  simp [leftSingularVector, smul_smul, ne_of_gt i.property]

theorem sum_positive_singularValues :
    (∑ i : PositiveSingularIndex A, singularValue A i.val) = Fn.nuclearNorm A := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => 0 < singularValue A i) (by simp)]
  change _ = ∑ i : Fin n, singularValue A i
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have h : ¬ 0 < singularValue A i := by simpa using hi
  exact le_antisymm (le_of_not_gt h) (singularValue_nonneg A i)

theorem image_eq_sum_positive (x : EuclideanSpace ℝ (Fin n)) :
    lin A x = ∑ i : PositiveSingularIndex A,
      ⟪rightSingularBasis A i.val, x⟫ •
        (singularValue A i.val • leftSingularVector A i) := by
  classical
  simp_rw [singularValue_smul_leftSingularVector]
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => 0 < singularValue A i) (by simp)
    (fun i => ⟪rightSingularBasis A i, x⟫ • lin A (rightSingularBasis A i))]
  have hexp : lin A x = ∑ i : Fin n,
      ⟪rightSingularBasis A i, x⟫ • lin A (rightSingularBasis A i) := by
    conv_lhs => rw [← (rightSingularBasis A).sum_repr x]
    simp only [map_sum, map_smul, OrthonormalBasis.repr_apply_apply]
  rw [hexp]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  have h : ¬ 0 < singularValue A i := by simpa using hi
  have hz : singularValue A i = 0 :=
    le_antisymm (le_of_not_gt h) (singularValue_nonneg A i)
  have hv : lin A (rightSingularBasis A i) = 0 := by
    apply norm_eq_zero.mp
    rw [norm_image_rightSingularBasis, hz]
  simp [hv]

theorem matrix_eq_sum_positive :
    A = ∑ i : PositiveSingularIndex A,
      singularValue A i.val • Matrix.vecMulVec
        (leftSingularVector A i).ofLp (rightSingularBasis A i.val).ofLp := by
  classical
  apply Matrix.toEuclideanLin.injective
  ext x j
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) => v j) (image_eq_sum_positive A x)
  simpa [lin, Matrix.toLpLin_apply, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, EuclideanSpace.inner_eq_star_dotProduct,
    Finset.sum_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc, dotProduct_comm] using h

/-- In one dimension, the nuclear norm is the absolute value of the entry. -/
theorem nuclearNorm_singleton (A : Matrix (Fin 1) (Fin 1) ℝ) :
    Fn.nuclearNorm A = |A 0 0| := by
  have hlin : Matrix.toEuclideanLin A (rightSingularBasis A 0) =
      A 0 0 • rightSingularBasis A 0 := by
    ext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  have h := norm_image_rightSingularBasis A 0
  change ‖Matrix.toEuclideanLin A (rightSingularBasis A 0)‖ = singularValue A 0 at h
  rw [hlin, norm_smul, (rightSingularBasis A).orthonormal.norm_eq_one, mul_one] at h
  simpa [Fn.nuclearNorm, singularValue] using h.symm

end Morew.Conic.Spectral
