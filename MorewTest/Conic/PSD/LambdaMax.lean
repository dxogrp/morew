/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.LambdaMax
import Morew.Conic.PSD.Representations
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Largest-eigenvalue certificates

Diagonal tests include negative eigenvalues, which distinguish the largest
eigenvalue from a spectral radius or an operator norm.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Conic.Spectral

open Matrix Morew.Conic.Spectral

example (n : Nat) (hn : 0 < n) (a : Fin n → ℝ) (t : ℝ) :
    Morew.Fn.lambdaMax (Matrix.diagonal a) ≤ t ↔ ∀ i, a i ≤ t := by
  rw [lambdaMax_le_iff _ (Matrix.isSymm_diagonal _) hn]
  have he : t • (1 : Matrix (Fin n) (Fin n) ℝ) - Matrix.diagonal a =
      Matrix.diagonal (fun i => t - a i) := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  simp [he, sub_nonneg]

example : Morew.Fn.lambdaMax (Matrix.diagonal ![-3, -2]) ≤ -1 := by
  apply (lambdaMax_le_iff _ (Matrix.isSymm_diagonal _) (by decide) _).mpr
  have he : (-1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - Matrix.diagonal ![-3, -2] =
      Matrix.diagonal ![2, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  rw [he]
  simp [Matrix.posSemidef_diagonal_iff, Fin.forall_fin_succ]

-- Repeated negative eigenvalues retain their sign and multiplicity; the atom
-- must not silently become a spectral radius or a matrix norm.
example : Morew.Fn.lambdaMax (Matrix.diagonal ![-3, -3]) = -3 := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![-3, -3]
  have hA : A.IsSymm := Matrix.isSymm_diagonal _
  have upper : Morew.Fn.lambdaMax A ≤ -3 := by
    apply (lambdaMax_le_iff A hA (by decide) (-3)).mpr
    have hz : (-3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - A = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [A]
    rw [hz]
    exact Matrix.PosSemidef.zero
  have lower := ((lambdaMax_le_iff A hA (by decide) (Morew.Fn.lambdaMax A)).mp
    le_rfl).diag_nonneg (i := 0)
  norm_num [A] at lower
  change Morew.Fn.lambdaMax A = -3
  linarith

example (n : Nat) (hn : 0 < n)
    (A : {A : Matrix (Fin n) (Fin n) ℝ // A.IsSymm}) (t : ℝ) :
    Morew.Fn.lambdaMax A.1 ≤ t ↔ ∃ u, (lambdaMaxEpigraph hn).target A t u :=
  (lambdaMaxEpigraph hn).source_iff_exists A t

end MorewTest.Conic.Spectral
