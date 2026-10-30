/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.SpectralNorm
import Morew.Conic.PSD.Representations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Native Euclidean matrix operator-norm certificates -/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Conic.SpectralNorm

open Morew Morew.Conic
open scoped Matrix.Norms.L2Operator

noncomputable section

example {m n : Nat} : (Spectral.spectralNormEpigraph (m := m) (n := n)).Auxiliary = Unit :=
  rfl

example {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) :
    (Spectral.spectralNormEpigraph).target A t () ↔
      0 ≤ t ∧ (fromBlocksFin (t • 1) A A.transpose (t • 1)).PosSemidef := Iff.rfl

example {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ) :
    ‖A‖ ≤ t ↔ ∃ auxiliary, Spectral.spectralNormEpigraph.target A t auxiliary :=
  Spectral.spectralNormEpigraph.source_iff_exists A t

example {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    (fromBlocksFin (0 : Matrix (Fin m) (Fin m) ℝ) A A.transpose
      (0 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ↔ A = 0 := by
  have h := Spectral.spectralNorm_le_iff A 0
  simpa only [zero_smul, le_refl, true_and, norm_le_zero_iff] using h.symm

example {m n : Nat} : Spectral.spectralNormEpigraph.target
    (0 : Matrix (Fin m) (Fin n) ℝ) 0 () := by
  exact (Spectral.spectralNorm_le_iff _ _).mp (by simp)

example (t : ℝ) : Spectral.spectralNormEpigraph.target
    (0 : Matrix (Fin 0) (Fin 0) ℝ) t () ↔ 0 ≤ t := by
  simpa only [Spectral.spectralNormEpigraph, norm_zero] using (Spectral.spectralNorm_le_iff
    (0 : Matrix (Fin 0) (Fin 0) ℝ) t).symm

example {n : Nat} (A : Matrix (Fin 0) (Fin n) ℝ) (t : ℝ) :
    Spectral.spectralNormEpigraph.target A t () ↔ 0 ≤ t := by
  have hA : A = 0 := Subsingleton.elim _ _
  subst A
  simpa only [Spectral.spectralNormEpigraph, norm_zero] using (Spectral.spectralNorm_le_iff
    (0 : Matrix (Fin 0) (Fin n) ℝ) t).symm

example {m : Nat} (A : Matrix (Fin m) (Fin 0) ℝ) (t : ℝ) :
    Spectral.spectralNormEpigraph.target A t () ↔ 0 ≤ t := by
  have hA : A = 0 := Subsingleton.elim _ _
  subst A
  simpa only [Spectral.spectralNormEpigraph, norm_zero] using (Spectral.spectralNorm_le_iff
    (0 : Matrix (Fin m) (Fin 0) ℝ) t).symm

example : ¬ Spectral.spectralNormEpigraph.target
    (0 : Matrix (Fin 0) (Fin 0) ℝ) (-1) () := by
  intro h
  have hnonnegative := h.1
  norm_num at hnonnegative

example (a t : ℝ) : |a| ≤ t ↔
    0 ≤ t ∧ (fromBlocksFin (t • 1) (!![a]) (!![a]).transpose (t • 1)).PosSemidef := by
  have hnorm : ‖(!![a] : Matrix (Fin 1) (Fin 1) ℝ)‖ = |a| := by
    have hdiag : (!![a] : Matrix (Fin 1) (Fin 1) ℝ) = Matrix.diagonal (fun _ => a) := by
      ext i j
      fin_cases i
      fin_cases j
      simp
    rw [hdiag, Matrix.l2_opNorm_diagonal]
    simp
  simpa only [hnorm] using Spectral.spectralNorm_le_iff (!![a]) t

-- The ordinary entrywise supremum norm of this matrix is four. The native L2
-- operator norm is larger, so this guards the norm instance in the source API.
example : 4 < ‖(!![3, 4] : Matrix (Fin 1) (Fin 2) ℝ)‖ := by
  have h := (Matrix.l2_opNorm_mulVec
    (!![3, 4] : Matrix (Fin 1) (Fin 2) ℝ)
    (WithLp.toLp 2 ![3, 4]))
  norm_num [EuclideanSpace.norm_eq, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at h
  have h25 : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5)]
  have h625 : Real.sqrt 625 = 25 := by
    rw [show (625 : ℝ) = 25 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 25)]
  rw [h25, h625] at h
  linarith

example (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    (i : Fin 2) (j : Fin 3) :
    fromBlocksFin (t • 1) A A.transpose (t • 1)
      (Fin.castAdd 3 i) (Fin.natAdd 2 j) = A i j := by
  simp

example (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    (i : Fin 2) (j : Fin 3) :
    fromBlocksFin (t • 1) A A.transpose (t • 1)
      (Fin.natAdd 2 j) (Fin.castAdd 3 i) = A i j := by
  simp

end

end MorewTest.Conic.SpectralNorm
