/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.LogDet
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Log-determinant semantics and exact certificates

The scalar and diagonal tests distinguish the totalized real logarithm from
its positive-definite modeling domain. A non-diagonal positive-definite matrix
exercises the triangular factorization needed for an attaining lift.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Conic.LogDet

open Matrix Morew Morew.Conic Morew.Conic.LogDet

private def HasLift {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Prop :=
  ∃ z : LowerTriangularEntries n, ∃ u : Fin n → ℝ,
    (fromBlocksFin X (lowerTriangularMatrix z) (lowerTriangularMatrix z).transpose
      (Matrix.diagonal (fun i => lowerTriangularMatrix z i i))).PosSemidef ∧
    (∀ i, (u i, 1, lowerTriangularMatrix z i i) ∈ EXP) ∧ t ≤ ∑ i, u i

private theorem hasLift_iff {n : Nat} (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hn : 0 < n) : HasLift X t ↔ X.PosDef ∧ t ≤ Fn.logDet X :=
  (hypograph_iff X t hn).symm

example (n : Nat) (hn : 0 < n) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosDef) (t : ℝ) : t ≤ Fn.logDet X ↔ HasLift X t :=
  le_logDet_iff X hX t hn

example (p : ℝ) : Fn.logDet (Matrix.diagonal (fun _ : Fin 1 => p)) = Real.log p := by
  simp [Fn.logDet]

example (n : Nat) (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) :
    Fn.logDet (Matrix.diagonal d) = ∑ i, Real.log (d i) := by
  simp only [Fn.logDet, Matrix.det_diagonal]
  exact Real.log_prod (fun i _ => (hd i).ne')

example (X : Matrix (Fin 0) (Fin 0) ℝ) : Fn.logDet X = 0 := by simp

example (X : Matrix (Fin 0) (Fin 0) ℝ) :
    ∃ (L : Matrix (Fin 0) (Fin 0) ℝ) (d : Fin 0 → ℝ),
      L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧ (∀ i, 0 < d i) ∧
        L * Matrix.diagonal d * L.transpose = X := by
  have hX : X = 1 := Subsingleton.elim _ _
  subst X
  exact exists_lower_diagonal_factor Matrix.PosDef.one

example (n : Nat) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosDef) :
    ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ X.det = ∏ i, d i := by
  obtain ⟨L, d, hL, hdiag, hd, hfactor⟩ := exists_lower_diagonal_factor hX
  exact ⟨d, hd, det_eq_prod_of_lower_diagonal_factor hL hdiag hfactor⟩

-- A determinant strictly between zero and one gives a negative log determinant.
example : Fn.logDet (Matrix.diagonal ![(1 / 2 : ℝ), 1 / 2]) < 0 := by
  rw [Fn.logDet]
  norm_num only [Matrix.det_diagonal, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  apply Real.log_neg <;> norm_num

-- The native totalized logarithm has a value at a singular matrix, but its
-- positive-definite modeling domain does not include that matrix.
example : Fn.logDet (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by simp [Fn.logDet]

example : ¬ (0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  intro h
  simpa using h.diag_pos (i := 0)

-- Positive determinant alone does not establish the positive-definite domain.
example : (Matrix.diagonal ![(-1 : ℝ), -1]).det = 1 := by norm_num

example : ¬ (Matrix.diagonal ![(-1 : ℝ), -1]).PosDef := by
  intro h
  have hdiag := h.diag_pos (i := 0)
  norm_num at hdiag

private theorem offDiagonal_posDef :
    (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  have h : (Matrix.vecMulVec (![1, 1] : Fin 2 → ℝ) ![1, 1]).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star (![1, 1] : Fin 2 → ℝ)
  convert (Matrix.PosDef.one : (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef).add_posSemidef h using 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.vecMulVec]

example : Fn.logDet (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) = Real.log 3 := by
  norm_num [Fn.logDet, Matrix.det_fin_two]

-- The scalar lift keeps exactly the positive domain and logarithmic bound.
example (p t : ℝ) :
    HasLift (Matrix.diagonal (fun _ : Fin 1 => p)) t ↔ 0 < p ∧ t ≤ Real.log p := by
  rw [hasLift_iff _ _ (by decide)]
  simp [Matrix.posDef_diagonal_iff, Fn.logDet]

-- This directly checks the scalar witness, including the exponential order.
example (p : ℝ) (hp : 0 < p) :
    HasLift (Matrix.diagonal (fun _ : Fin 1 => p)) (Real.log p) := by
  refine ⟨fun _ => p, fun _ => Real.log p, ?_, ?_, by simp⟩
  · rw [posSemidef_fromBlocksFin_iff]
    let v : Fin 1 ⊕ Fin 1 → ℝ := fun _ => 1
    have h : (Matrix.vecMulVec v v).PosSemidef := by
      simpa using Matrix.posSemidef_vecMulVec_self_star v
    convert h.smul hp.le using 1
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [lowerTriangularMatrix, Matrix.vecMulVec, v]
  · intro i
    simpa [lowerTriangularMatrix] using
      (Morew.Conic.Exponential.le_log_iff p (Real.log p) hp).mp le_rfl

example (n : Nat) (hn : 0 < n) (t : ℝ) :
    HasLift (1 : Matrix (Fin n) (Fin n) ℝ) t ↔ t ≤ 0 := by
  rw [hasLift_iff _ _ hn]
  simp [Matrix.PosDef.one, Fn.logDet]

example : HasLift (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) (Real.log 3) := by
  rw [hasLift_iff _ _ (by decide)]
  exact ⟨offDiagonal_posDef, by norm_num [Fn.logDet, Matrix.det_fin_two]⟩

example (t : ℝ) : ¬ HasLift (0 : Matrix (Fin 1) (Fin 1) ℝ) t := by
  rw [hasLift_iff _ _ (by decide)]
  rintro ⟨h, _⟩
  simpa using h.diag_pos (i := 0)

example (t : ℝ) : ¬ HasLift (Matrix.diagonal ![(-1 : ℝ), -1]) t := by
  rw [hasLift_iff _ _ (by decide)]
  rintro ⟨h, _⟩
  have hdiag := h.diag_pos (i := 0)
  norm_num at hdiag

-- Symmetry is part of the source domain even when the determinant is positive.
example (t : ℝ) : ¬ HasLift (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) t := by
  rw [hasLift_iff _ _ (by decide)]
  rintro ⟨h, _⟩
  have hsym := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A 0 1) h.isHermitian.eq
  norm_num [Matrix.conjTranspose_apply] at hsym

-- Attainment permits negative log determinants; the same matrix cannot
-- satisfy a zero lower bound.
example : HasLift (Matrix.diagonal ![(1 / 2 : ℝ), 1 / 2]) (Real.log (1 / 4)) := by
  rw [hasLift_iff _ _ (by decide)]
  constructor
  · simp [Matrix.posDef_diagonal_iff, Fin.forall_fin_succ]
  · norm_num [Fn.logDet]

example : ¬ HasLift (Matrix.diagonal ![(1 / 2 : ℝ), 1 / 2]) 0 := by
  rw [hasLift_iff _ _ (by decide)]
  rintro ⟨_, h⟩
  have hneg : Fn.logDet (Matrix.diagonal ![(1 / 2 : ℝ), 1 / 2]) < 0 := by
    norm_num only [Fn.logDet, Matrix.det_diagonal, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    apply Real.log_neg <;> norm_num
  exact (not_lt_of_ge h) hneg

end MorewTest.Conic.LogDet
