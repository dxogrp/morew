/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.PSD.MatrixFraction
import Morew.Conic.PSD.Representations
import Morew.Conic.PSD.PositiveDefinite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Matrix-fraction and positive-definite domain certificates

These tests exercise symbolic dimensions, scalar semantics, singular pivots,
and the empty-dimensional boundary without installing the DSL.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Conic.MatrixFraction

open Matrix Morew.Conic

example (n : Nat) (x : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (t : ℝ) :
    Morew.Fn.matrixFrac x P ≤ t ↔
      (fromBlocksFin P (fun (i : Fin n) (_ : Fin 1) => x i) (fun _ : Fin 1 => x)
        (Matrix.diagonal (fun _ : Fin 1 => t))).PosSemidef :=
  Morew.Conic.MatrixFraction.matrixFrac_le_iff x P hP t

example (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) :
    P.PosDef ↔ ∃ W : SymmetricMatrix n,
      (fromBlocksFin P 1 1 W.toMatrix).PosSemidef :=
  positiveDefiniteLift.source_iff_exists P

example (n : Nat) (P W : Matrix (Fin n) (Fin n) ℝ)
    (h : (fromBlocksFin P 1 1 W).PosSemidef) : P.PosDef :=
  posDef_of_fromBlocksFin_identity_posSemidef P W h

example (x p : ℝ) :
    Morew.Fn.matrixFrac ![x] (Matrix.diagonal (fun _ : Fin 1 => p)) = x ^ 2 / p := by
  simp [Morew.Fn.matrixFrac, Matrix.mulVec, dotProduct,
    pow_two, div_eq_mul_inv]
  ring

example (x : Fin 0 → ℝ) (P : Matrix (Fin 0) (Fin 0) ℝ) (t : ℝ) :
    Morew.Fn.matrixFrac x P ≤ t ↔ 0 ≤ t := by simp

example (P : Matrix (Fin 0) (Fin 0) ℝ) :
    ∃ W : SymmetricMatrix 0, (fromBlocksFin P 1 1 W.toMatrix).PosSemidef := by
  apply (posDef_iff_exists_identity_block P).mp
  have hP : P = 1 := Subsingleton.elim _ _
  rw [hP]
  exact Matrix.PosDef.one

example : Morew.Fn.matrixFrac ![1] (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0 := by
  simp [Morew.Fn.matrixFrac]

example (t : ℝ) :
    ¬ (fromBlocksFin (0 : Matrix (Fin 1) (Fin 1) ℝ) 1 1
      (Matrix.diagonal (fun _ : Fin 1 => t))).PosSemidef := by
  intro h
  have hP := posDef_of_fromBlocksFin_identity_posSemidef _ _ h
  have hpositive := hP.diag_pos (i := 0)
  simp at hpositive

end MorewTest.Conic.MatrixFraction
