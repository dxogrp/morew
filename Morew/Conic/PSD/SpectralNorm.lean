/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Exact epigraph of the Euclidean matrix operator norm -/

namespace Morew.Conic.Spectral

open Matrix
open scoped Matrix.Norms.L2Operator

private theorem dot_self_eq_norm_sq {n : Nat} (x : Fin n → ℝ) :
    x ⬝ᵥ x = ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

private theorem block_quadratic {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ)
    (t : ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    star (Sum.elim u v) ⬝ᵥ
        (Matrix.fromBlocks (t • 1) A A.transpose (t • 1) *ᵥ Sum.elim u v) =
      t * (u ⬝ᵥ u) + 2 * (u ⬝ᵥ (A *ᵥ v)) + t * (v ⬝ᵥ v) := by
  simp only [star_trivial, Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl,
    Sum.elim_inr, Matrix.smul_mulVec, Matrix.one_mulVec,
    sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_smul,
    Matrix.dotProduct_transpose_mulVec, smul_eq_mul]
  ring

private theorem block_posSemidef_iff {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) :
    (Matrix.fromBlocks (t • 1) A A.transpose (t • 1)).PosSemidef ↔
      ∀ (u : Fin m → ℝ) (v : Fin n → ℝ),
        0 ≤ t * (u ⬝ᵥ u) + 2 * (u ⬝ᵥ (A *ᵥ v)) + t * (v ⬝ᵥ v) := by
  constructor
  · intro h u v
    simpa only [block_quadratic] using h.dotProduct_mulVec_nonneg (Sum.elim u v)
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · apply Matrix.isHermitian_iff_isSymm.mpr
      exact (Matrix.isSymm_one.smul t).fromBlocks rfl (Matrix.isSymm_one.smul t)
    · intro x
      have hx : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := by
        funext i
        cases i <;> rfl
      rw [hx, block_quadratic]
      exact h _ _

/-- A rectangular Euclidean operator-norm upper bound is exactly the usual
symmetric PSD block, together with a nonnegative bound. The scalar row retains
the correct meaning when both matrix dimensions are zero. -/
theorem spectralNorm_le_iff {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) :
    ‖A‖ ≤ t ↔ 0 ≤ t ∧
      (fromBlocksFin (t • 1) A A.transpose (t • 1)).PosSemidef := by
  rw [posSemidef_fromBlocksFin_iff, block_posSemidef_iff]
  constructor
  · intro h
    have ht : 0 ≤ t := (norm_nonneg A).trans h
    refine ⟨ht, fun u v => ?_⟩
    let u' : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 u
    let v' : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
    let w : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (A *ᵥ v)
    have hw : ‖w‖ ≤ t * ‖v'‖ :=
      (A.l2_opNorm_mulVec v').trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    have hc : -(‖u'‖ * ‖w‖) ≤ u ⬝ᵥ (A *ᵥ v) := by
      have hc := neg_le_of_abs_le (abs_real_inner_le_norm w u')
      simpa [EuclideanSpace.inner_eq_star_dotProduct, u', w, mul_comm] using hc
    have hm := mul_le_mul_of_nonneg_left hw (norm_nonneg u')
    rw [dot_self_eq_norm_sq u, dot_self_eq_norm_sq v]
    change 0 ≤ t * ‖u'‖ ^ 2 + 2 * (u ⬝ᵥ (A *ᵥ v)) + t * ‖v'‖ ^ 2
    nlinarith [mul_nonneg ht (sq_nonneg (‖u'‖ - ‖v'‖))]
  · rintro ⟨ht, h⟩
    rw [Matrix.l2_opNorm_def]
    apply ContinuousLinearMap.opNorm_le_bound _ ht
    intro v
    change ‖WithLp.toLp 2 (A *ᵥ WithLp.ofLp v)‖ ≤ t * ‖v‖
    let w : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (A *ᵥ WithLp.ofLp v)
    change ‖w‖ ≤ t * ‖v‖
    by_cases hz : t = 0
    · subst t
      have hv := h (-(A *ᵥ WithLp.ofLp v)) (WithLp.ofLp v)
      simp only [zero_mul, zero_add, add_zero, neg_dotProduct] at hv
      rw [dot_self_eq_norm_sq] at hv
      change 0 ≤ 2 * -‖w‖ ^ 2 at hv
      have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
      simp [this]
    · have ht' : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
      have hv := h (-(A *ᵥ WithLp.ofLp v)) (t • WithLp.ofLp v)
      simp only [neg_dotProduct, dotProduct_neg, neg_neg, Matrix.mulVec_smul,
        dotProduct_smul, smul_dotProduct, smul_eq_mul] at hv
      rw [dot_self_eq_norm_sq, dot_self_eq_norm_sq] at hv
      change 0 ≤ t * ‖w‖ ^ 2 + 2 * (t * -‖w‖ ^ 2) +
        t * (t * (t * ‖v‖ ^ 2)) at hv
      have hs : 0 ≤ t ^ 2 * ‖v‖ ^ 2 - ‖w‖ ^ 2 := by
        apply nonneg_of_mul_nonneg_left (b := t) ?_ ht'
        nlinarith [hv]
      have hn : 0 ≤ t * ‖v‖ := mul_nonneg ht (norm_nonneg v)
      nlinarith [norm_nonneg w]

end Morew.Conic.Spectral
