/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Fn.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Named vector norm semantics

The functions retain the canonical norms independently of caller instances.
Empty vectors, signed singleton vectors, and a shared nonzero vector distinguish
their exact mathematical meanings.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Fn.Norm

open Morew

noncomputable section

example {n : Nat} (x : Fin n → ℝ) : Fn.norm1 x = ‖WithLp.toLp 1 x‖ := rfl

example {n : Nat} (x : Fin n → ℝ) : Fn.norm2 x = ‖WithLp.toLp 2 x‖ := rfl

example {n : Nat} (x : Fin n → ℝ) : Fn.normInf x = ‖x‖ := rfl

example {n : Nat} (x : Fin n → ℝ) :
    0 ≤ Fn.norm1 x ∧ 0 ≤ Fn.norm2 x ∧ 0 ≤ Fn.normInf x :=
  ⟨Fn.norm1_nonneg x, Fn.norm2_nonneg x, Fn.normInf_nonneg x⟩

example {n : Nat} :
    Fn.norm1 (0 : Fin n → ℝ) = 0 ∧ Fn.norm2 (0 : Fin n → ℝ) = 0 ∧
      Fn.normInf (0 : Fin n → ℝ) = 0 := by simp

example (x : Fin 0 → ℝ) (t : ℝ) :
    (Fn.norm1 x ≤ t ↔ 0 ≤ t) ∧ (Fn.norm2 x ≤ t ↔ 0 ≤ t) ∧
      (Fn.normInf x ≤ t ↔ 0 ≤ t) := by simp

example (x : Fin 0 → ℝ) :
    ¬ Fn.norm1 x ≤ -1 ∧ ¬ Fn.norm2 x ≤ -1 ∧ ¬ Fn.normInf x ≤ -1 := by simp

example (a : ℝ) : Fn.norm1 ![a] = |a| := by
  simp [Fn.norm1_eq_sum_abs]

example (a : ℝ) : Fn.norm2 ![a] = |a| := by
  apply (sq_eq_sq₀ (Fn.norm2_nonneg _) (abs_nonneg _)).mp
  simp [Fn.norm2_sq_eq_sum]

example (a : ℝ) : Fn.normInf ![a] = |a| := by
  have h : (![a] : Fin 1 → ℝ) = fun _ => a := by
    ext i
    fin_cases i
    rfl
  rw [Fn.normInf, h]
  exact (pi_norm_const _).trans (Real.norm_eq_abs _)

theorem norm1_three_four : Fn.norm1 ![3, 4] = 7 := by
  norm_num [Fn.norm1_eq_sum_abs, Fin.sum_univ_succ]

theorem norm2_three_four : Fn.norm2 ![3, 4] = 5 := by
  apply (sq_eq_sq₀ (Fn.norm2_nonneg _) (by norm_num)).mp
  norm_num [Fn.norm2_sq_eq_sum, Fin.sum_univ_succ]

theorem normInf_three_four : Fn.normInf ![3, 4] = 4 := by
  apply le_antisymm
  · rw [Fn.normInf, pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    fin_cases i <;> norm_num
  · simpa [Fn.normInf] using (norm_le_pi_norm (![3, 4] : Fin 2 → ℝ) 1)

/-! Conflicting local norm operations cannot change the named functions. -/

section CapturedInstances

local instance : Norm ℝ := ⟨fun _ => 101⟩
local instance : Norm (Fin 2 → ℝ) := ⟨fun _ => 102⟩
local instance : Norm (WithLp 1 (Fin 2 → ℝ)) := ⟨fun _ => 103⟩
local instance : Norm (WithLp 2 (Fin 2 → ℝ)) := ⟨fun _ => 104⟩

example : ‖(3 : ℝ)‖ = 101 := rfl
example : ‖(![3, 4] : Fin 2 → ℝ)‖ = 102 := rfl
example : ‖WithLp.toLp 1 (![3, 4] : Fin 2 → ℝ)‖ = 103 := rfl
example : ‖WithLp.toLp 2 (![3, 4] : Fin 2 → ℝ)‖ = 104 := rfl

example : Fn.norm1 ![3, 4] = 7 := norm1_three_four
example : Fn.norm2 ![3, 4] = 5 := norm2_three_four
example : Fn.normInf ![3, 4] = 4 := normInf_three_four

end CapturedInstances

end

end MorewTest.Fn.Norm
