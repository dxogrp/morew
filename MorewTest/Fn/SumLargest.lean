/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Fn.SumLargest
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Sum-largest values, threshold attainment, and epigraph endpoints -/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Fn.SumLargest

open Morew

noncomputable section

private theorem tied_antitone : Antitone (![3, 3, -2] : Fin 3 → ℝ) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def] at *

private theorem tied_value : Fn.sumLargest 2 ![3, 3, -2] = 6 := by
  rw [Fn.sumLargest_eq_sum_of_antitone 2 _ tied_antitone]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

example : Fn.sumLargest 2 ![-2, 3, 3] = 6 := by
  have h : (![3, 3, -2] : Fin 3 → ℝ) ∘ Equiv.swap 0 2 = ![-2, 3, 3] := by
    ext i
    fin_cases i <;> norm_num [Equiv.swap_apply_def, Fin.ext_iff, Matrix.cons_val]
  rw [← h, Fn.sumLargest_comp_perm]
  exact tied_value

example : Fn.sumLargest 2 ![4, 1, -3] = 5 := by
  rw [Fn.sumLargest_eq_sum_of_antitone 2 _ (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def] at *)]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

private theorem negative_value : Fn.sumLargest 2 ![-1, -3, -5] = -4 := by
  rw [Fn.sumLargest_eq_sum_of_antitone 2 _ (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.le_def] at *)]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

example (k : Nat) (x : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    Fn.sumLargest k (x ∘ σ) = Fn.sumLargest k x := Fn.sumLargest_comp_perm k x σ

example (x : Fin n → ℝ) : Fn.sumLargest 0 x = 0 := by simp

example (k : Nat) (x : Fin 0 → ℝ) : Fn.sumLargest k x = 0 := by simp

example (x : Fin n → ℝ) : Fn.sumLargest n x = ∑ i, x i :=
  Fn.sumLargest_of_le n x (le_refl n)

example : Fn.sumLargest 5 ![-2, 3, 3] = 4 := by
  rw [Fn.sumLargest_of_le 5 _ (by decide)]
  norm_num [Fin.sum_univ_succ]

example : Fn.sumLargest 1 ![3, 3, -2] = 3 := by
  rw [Fn.sumLargest_eq_sum_of_antitone 1 _ tied_antitone]
  norm_num [Finset.sum_filter, Fin.sum_univ_succ]

example (x : Fin n → ℝ) (hn : 0 < n) :
    Fn.sumLargest 1 x = Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ x :=
  Fn.sumLargest_one x hn

/-! Ties and negative thresholds both attain the minimum. -/

example : Fn.sumLargest 2 ![3, 3, -2] =
    (2 : ℝ) * 3 + ∑ i : Fin 3, max ((![3, 3, -2] : Fin 3 → ℝ) i - 3) 0 := by
  rw [tied_value]
  norm_num [Fin.sum_univ_succ]

example : Fn.sumLargest 2 ![-1, -3, -5] =
    (2 : ℝ) * (-3) + ∑ i : Fin 3, max ((![-1, -3, -5] : Fin 3 → ℝ) i - (-3)) 0 := by
  rw [negative_value]
  norm_num [Fin.sum_univ_succ]

example (k : Nat) (x : Fin n → ℝ) (hk : k ≤ n) :
    ∃ τ : ℝ, Fn.sumLargest k x = (k : ℝ) * τ + ∑ i, max (x i - τ) 0 :=
  Fn.sumLargest_exists_threshold k x hk

example (k : Nat) (x : Fin n → ℝ) (hk : k ≤ n) :
    IsLeast (Set.range fun τ : ℝ => (k : ℝ) * τ + ∑ i, max (x i - τ) 0)
      (Fn.sumLargest k x) := Fn.sumLargest_isLeast_threshold k x hk

example (x : Fin n → ℝ) (t : ℝ) :
    (∃ τ : ℝ, ∃ u : Fin n → ℝ,
      (∀ i, 0 ≤ u i) ∧ (∀ i, x i - τ ≤ u i) ∧ (∑ i, u i) ≤ t) ↔ 0 ≤ t := by
  simpa using (Fn.sumLargest_le_iff 0 x t (Nat.zero_le n)).symm

example (x : Fin n → ℝ) (t : ℝ) :
    (∃ τ : ℝ, ∃ u : Fin n → ℝ,
      (∀ i, 0 ≤ u i) ∧ (∀ i, x i - τ ≤ u i) ∧
        (n : ℝ) * τ + (∑ i, u i) ≤ t) ↔ (∑ i, x i) ≤ t := by
  simpa only [Fn.sumLargest_of_le n x (le_refl n)] using
    (Fn.sumLargest_le_iff n x t (le_refl n)).symm

example (x : Fin 0 → ℝ) (t : ℝ) :
    (∃ τ : ℝ, ∃ u : Fin 0 → ℝ,
      (∀ i, 0 ≤ u i) ∧ (∀ i, x i - τ ≤ u i) ∧
        (0 : ℝ) * τ + (∑ i, u i) ≤ t) ↔ 0 ≤ t := by
  simpa only [Fn.sumLargest_empty, Nat.cast_zero] using
    (Fn.sumLargest_le_iff 0 x t (le_refl 0)).symm

example (x : Fin 0 → ℝ) :
    ¬ ∃ τ : ℝ, ∃ u : Fin 0 → ℝ,
      (∀ i, 0 ≤ u i) ∧ (∀ i, x i - τ ≤ u i) ∧
        (0 : ℝ) * τ + (∑ i, u i) ≤ -1 := by
  simp

end

end MorewTest.Fn.SumLargest
