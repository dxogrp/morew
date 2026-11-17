/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Fn.Cvar
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Empirical CVaR values and attained thresholds

Integer and fractional tail masses include ties, signed losses, and tails smaller
than one sample. The function's infimum definition remains independent of the DSL.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Fn.Cvar

open Morew

noncomputable section

example (β : ℝ) (x : Fin n → ℝ) :
    Fn.cvar β x = sInf (Set.range fun τ : ℝ =>
      τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β))) := rfl

variable (β : ℝ) (x : Fin n → ℝ) (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1)

example : 0 < (n : ℝ) * (1 - β) :=
  mul_pos (Nat.cast_pos.mpr hn) (sub_pos.mpr hβ.2)

example : BddBelow (Set.range fun τ : ℝ =>
    τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β))) :=
  Fn.cvar_bddBelow_threshold β x hn hβ

example : IsLeast (Set.range fun τ : ℝ =>
    τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β))) (Fn.cvar β x) :=
  Fn.cvar_isLeast_threshold β x hn hβ

example : ∃ τ : ℝ, Fn.cvar β x =
    τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β)) :=
  Fn.cvar_exists_threshold β x hn hβ

example (τ : ℝ) : Fn.cvar β x ≤
    τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β)) :=
  Fn.cvar_le_threshold β x τ hn hβ

example (t : ℝ) : Fn.cvar β x ≤ t ↔ ∃ τ : ℝ, ∃ u : Fin n → ℝ,
    (∀ i, 0 ≤ u i) ∧ (∀ i, x i - τ ≤ u i) ∧
      τ + (∑ i, u i) / ((n : ℝ) * (1 - β)) ≤ t :=
  Fn.cvar_le_iff β x t hn hβ

example : Fn.cvar 0 x = (∑ i, x i) / n := Fn.cvar_zero x hn

example (k : Nat) (hk : 1 ≤ k ∧ k ≤ n)
    (hq : (n : ℝ) * (1 - β) = k) :
    Fn.cvar β x = Fn.sumLargest k x / k :=
  Fn.cvar_eq_sumLargest_div β x k hn hβ hk hq

private theorem tied_antitone : Antitone (![3, 3, -2] : Fin 3 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def] at *

private theorem negative_antitone : Antitone (![-1, -3, -5] : Fin 3 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def] at *

example : Fn.cvar (1 / 3) ![3, 3, -2] = 3 := by
  rw [Fn.cvar_eq_sumLargest_div (1 / 3) _ 2 (by decide) (by norm_num)
    (by decide) (by norm_num)]
  rw [Fn.sumLargest_eq_sum_of_antitone 2 _ tied_antitone]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

example : Fn.cvar (1 / 3) ![-1, -3, -5] = -2 := by
  rw [Fn.cvar_eq_sumLargest_div (1 / 3) _ 2 (by decide) (by norm_num)
    (by decide) (by norm_num)]
  rw [Fn.sumLargest_eq_sum_of_antitone 2 _ negative_antitone]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

example : Fn.cvar 0 ![-2, 1, 4] = 1 := by
  rw [Fn.cvar_zero _ (by decide)]
  norm_num [Fin.sum_univ_succ]

private theorem fractional_antitone : Antitone (![3, 1, 0] : Fin 3 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def] at *

private theorem reverse_fractional :
    ((![3, 1, 0] : Fin 3 → ℝ) ∘ Equiv.swap 0 2) = ![0, 1, 3] := by
  ext i
  fin_cases i <;> norm_num [Equiv.swap_apply_def, Fin.ext_iff, Matrix.cons_val]

private theorem fractional_largest_one : Fn.sumLargest 1 ![0, 1, 3] = 3 := by
  rw [← reverse_fractional, Fn.sumLargest_comp_perm]
  rw [Fn.sumLargest_eq_sum_of_antitone 1 _ fractional_antitone]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

private theorem fractional_largest_two : Fn.sumLargest 2 ![0, 1, 3] = 4 := by
  rw [← reverse_fractional, Fn.sumLargest_comp_perm]
  rw [Fn.sumLargest_eq_sum_of_antitone 2 _ fractional_antitone]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

private theorem fractional_value : Fn.cvar (1 / 2) ![0, 1, 3] = 7 / 3 := by
  rw [Fn.cvar_eq_interpolate_sumLargest (1 / 2) _ 1 (by decide) (by norm_num)
    (by decide) (by norm_num) (by norm_num)]
  rw [fractional_largest_one, fractional_largest_two]
  norm_num

example : Fn.cvar (1 / 2) ![0, 1, 3] = 7 / 3 := fractional_value

-- Threshold one attains the fractional-tail value, with excess vector (0, 0, 2).
example : Fn.cvar (1 / 2) ![0, 1, 3] =
    1 + (∑ i : Fin 3, max ((![0, 1, 3] : Fin 3 → ℝ) i - 1) 0) /
      ((3 : ℝ) * (1 - 1 / 2)) := by
  rw [fractional_value]
  norm_num [Fin.sum_univ_succ]

-- A tail mass of three quarters lies entirely in the largest sample.
example : Fn.cvar (3 / 4) ![0, 1, 3] = 3 := by
  rw [Fn.cvar_eq_interpolate_sumLargest (3 / 4) _ 0 (by decide) (by norm_num)
    (by decide) (by norm_num) (by norm_num)]
  rw [Fn.sumLargest_zero_left, fractional_largest_one]
  norm_num

example : Fn.cvar (1 / 2) ![-4, -4, -4] = -4 := by
  rw [Fn.cvar_eq_interpolate_sumLargest (1 / 2) _ 1 (by decide) (by norm_num)
    (by decide) (by norm_num) (by norm_num)]
  rw [Fn.sumLargest_eq_sum_of_antitone 1 _ (by
    intro i j _; fin_cases i <;> fin_cases j <;> norm_num)]
  rw [Fn.sumLargest_eq_sum_of_antitone 2 _ (by
    intro i j _; fin_cases i <;> fin_cases j <;> norm_num)]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

example (c β : ℝ) (hβ : 0 ≤ β ∧ β < 1) : Fn.cvar β ![c] = c := by
  rw [Fn.cvar_eq_interpolate_sumLargest β _ 0 (by decide) hβ
    (by decide) (by norm_num; linarith [hβ.2]) (by norm_num; linarith [hβ.1])]
  rw [Fn.sumLargest_zero_left, Fn.sumLargest_of_le 1 _ (le_refl 1)]
  simp [ne_of_gt (sub_pos.mpr hβ.2)]

end

end MorewTest.Fn.Cvar
