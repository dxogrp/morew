/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic
import Mathlib.Tactic.NormNum

/-!
# Exponential cones and exact finite representations

The public semantic API certifies finite representations independently of the
modeling language. Counterexamples distinguish totalized real formulas from
their logarithm and entropy domains.
-/

assert_not_exists Morew.ConstraintRepr Morew.Syntax.ProblemView

namespace MorewTest.Conic.Exponential

open Morew Morew.Conic Morew.Conic.Exponential

noncomputable section

example (a t : ℝ) : Real.exp a ≤ t ↔ (a, 1, t) ∈ EXP := exp_le_iff a t

example (a t : ℝ) (ha : 0 < a) :
    t ≤ Real.log a ↔ (t, 1, a) ∈ EXP := le_log_iff a t ha

example (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log (a / b) ≤ t ↔ (-t, a, b) ∈ EXP :=
  relEntr_le_iff a b t ha hb

example (b t : ℝ) (hb : 0 ≤ b) :
    Fn.relEntr 0 b ≤ t ↔ (-t, 0, b) ∈ EXP :=
  relEntr_zero_le_iff b t hb

example (t : ℝ) : Fn.relEntr 0 0 ≤ t ↔ (-t, 0, 0) ∈ EXP :=
  relEntr_zero_le_iff 0 t le_rfl

example (a : ℝ) : Fn.relEntr a 1 = -Real.negMulLog a :=
  Fn.relEntr_one_right a

example (a t : ℝ) (ha : 0 ≤ a) :
    t ≤ Real.negMulLog a ↔ (t, a, 1) ∈ EXP :=
  le_negMulLog_iff a t ha

example (a : ℝ) : Fn.entr a = Real.negMulLog a := rfl

example : Fn.entr 0 = 0 ∧ Fn.entr 1 = 0 := by simp

example (a t : ℝ) (ha : 0 ≤ a) :
    t ≤ Fn.entr a ↔ (t, a, 1) ∈ EXP :=
  le_entr_iff a t ha

example (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Fn.klDiv a b ≤ t ↔ (b - a - t, a, b) ∈ EXP :=
  klDiv_le_iff a b t ha hb

example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ Fn.klDiv a b :=
  Fn.klDiv_nonneg a b ha hb

example (a b : ℝ) : Fn.klDiv 0 b = b ∧ Fn.klDiv a a = 0 := by simp

example (t : ℝ) : t ≤ 0 ↔ (t, 0, 1) ∈ EXP := by
  simp

example (b t : ℝ) (hb : 0 < b) : b ≤ t ↔ (b - t, 0, b) ∈ EXP := by
  simpa using klDiv_le_iff 0 b t le_rfl hb

/-! Totalized logarithm and entropy values extend beyond their modeling domains. -/

example : (0 : ℝ) ≤ Real.log 0 := by simp
example : ¬ ((0 : ℝ), 1, 0) ∈ EXP := by norm_num
example : Fn.relEntr 1 0 ≤ 0 := by simp [Fn.relEntr]
example : ¬ (-(0 : ℝ), 1, 0) ∈ EXP := by norm_num
example : Fn.relEntr 1 (-1) ≤ 0 := by simp [Fn.relEntr]
example : ¬ (-(0 : ℝ), 1, -1) ∈ EXP := by norm_num
example : Real.negMulLog (-1) = 0 := by simp [Real.negMulLog]
example : ¬ ((0 : ℝ), -1, 1) ∈ EXP := by norm_num
example : Fn.klDiv 1 0 = -1 := by norm_num [Fn.klDiv, Fn.relEntr]
example : ¬ ((0 : ℝ) - 1 - (-1), 1, 0) ∈ EXP := by norm_num

/-! Finite representations retain one grouped row and one scalar sum. -/

example {n : Nat} (x : Fin n → ℝ) (t : ℝ) (hx : ∀ i, 0 ≤ x i) :
    t ≤ ∑ i, Fn.entr (x i) ↔
      ∃ u : Fin n → ℝ, (∀ i, (u i, x i, 1) ∈ EXP) ∧ t ≤ ∑ i, u i :=
  le_sum_entr_iff x t hx

example {n : Nat} (x q : Fin n → ℝ) (t : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hq : ∀ i, 0 < q i) :
    (∑ i, Fn.klDiv (x i) (q i)) ≤ t ↔
      ∃ u : Fin n → ℝ,
        (∀ i, (q i - x i - u i, x i, q i) ∈ EXP) ∧ (∑ i, u i) ≤ t :=
  sum_klDiv_le_iff x q t hx hq

example (a t : ℝ) (ha : 0 ≤ a) :
    (∃ u : Fin 1 → ℝ, (∀ i, (u i, a, 1) ∈ EXP) ∧ t ≤ ∑ i, u i) ↔
      t ≤ Fn.entr a := by
  simpa using (le_sum_entr_iff (fun _ : Fin 1 => a) t (fun _ => ha)).symm

example (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    (∃ u : Fin 1 → ℝ, (∀ i, (b - a - u i, a, b) ∈ EXP) ∧ (∑ i, u i) ≤ t) ↔
      Fn.klDiv a b ≤ t := by
  simpa using (sum_klDiv_le_iff (fun _ : Fin 1 => a) (fun _ => b) t
    (fun _ => ha) (fun _ => hb)).symm

example (x : Fin 0 → ℝ) (t : ℝ) :
    (∃ u : Fin 0 → ℝ, (∀ i, (u i, x i, 1) ∈ EXP) ∧ t ≤ ∑ i, u i) ↔ t ≤ 0 := by
  rw [← le_sum_entr_iff x t (fun i => Fin.elim0 i)]
  simp

example (x q : Fin 0 → ℝ) (t : ℝ) :
    (∃ u : Fin 0 → ℝ,
      (∀ i, (q i - x i - u i, x i, q i) ∈ EXP) ∧ (∑ i, u i) ≤ t) ↔ 0 ≤ t := by
  rw [← sum_klDiv_le_iff x q t (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)]
  simp

example (x : Fin 0 → ℝ) :
    ¬ ∃ u : Fin 0 → ℝ, (∀ i, (u i, x i, 1) ∈ EXP) ∧ 1 ≤ ∑ i, u i := by
  simp

example (x q : Fin 0 → ℝ) :
    ¬ ∃ u : Fin 0 → ℝ,
      (∀ i, (q i - x i - u i, x i, q i) ∈ EXP) ∧ (∑ i, u i) ≤ -1 := by
  simp

example {n : Nat} (xs : Fin n → ℝ) (t : ℝ) (hn : 0 < n) :
    Real.log (∑ i, Real.exp (xs i)) ≤ t ↔
      ∃ u : Fin n → ℝ,
        (∀ i, (xs i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 :=
  logSumExp_le_iff xs t hn

example (a t : ℝ) :
    Real.log (1 + Real.exp a) ≤ t ↔
      ∃ u : Fin 2 → ℝ,
        (∀ i, (![0, a] i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 :=
  softplus_le_iff a t

example (a : ℝ) : Fn.logSumExp ![a] = a := by
  simp [Fn.logSumExp]

example (xs : Fin 0 → ℝ) : Fn.logSumExp xs = 0 := by
  simp [Fn.logSumExp]

example (xs : Fin 0 → ℝ) : ¬ Fn.logSumExp xs ≤ -1 := by
  simp [Fn.logSumExp]

example (xs : Fin 0 → ℝ) (t : ℝ) :
    ∃ u : Fin 0 → ℝ,
      (∀ i, (xs i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 := by
  exact ⟨0, fun i => Fin.elim0 i, by simp⟩

/-! Manual forms certify affine data for both objective senses. -/

def exponentialRow : Constraint (ℝ × ℝ) where
  cone := Cone.exponential
  map := AffineMap.fst.prod ((AffineMap.const ℝ (ℝ × ℝ) 1).prod AffineMap.snd)

def minimumData : Data (ℝ × ℝ) where
  sense := .minimize
  objective := AffineMap.snd
  rowCount := 1
  constraints := fun _ => exponentialRow

def minimum : Problem (ℝ × ℝ) ℝ where
  objective := fun p => p.2
  feasible := fun p => ∀ _ : Fin 1, exponentialRow.Holds p

def minimumForm : Form minimum where
  data := minimumData
  represents := rfl

example : minimumForm.data.sense = .minimize := rfl
example : minimumData.toProblem = minimum := minimumForm.represents
example : IsConic minimum := minimumForm.isConic

example (p : ℝ × ℝ) : minimum.feasible p ↔ Real.exp p.1 ≤ p.2 := by
  change (∀ _ : Fin 1, (p.1, 1, p.2) ∈ EXP) ↔ _
  simp

example : Convex ℝ {p | minimumData.toProblem.feasible p} :=
  minimumData.feasibleSetConvex

def maximumData : Data (ℝ × ℝ) where
  sense := .maximize
  objective := AffineMap.fst
  rowCount := 1
  constraints := fun _ => exponentialRow

def maximum : Problem (ℝ × ℝ) (OrderDual ℝ) where
  objective := fun p => p.1
  feasible := fun p => ∀ _ : Fin 1, exponentialRow.Holds p

def maximumForm : Form maximum where
  data := maximumData
  represents := rfl

example : maximumForm.data.sense = .maximize := rfl
example : maximumData.toProblem = maximum := maximumForm.represents
example : IsConic maximum := maximumForm.isConic

end
end MorewTest.Conic.Exponential
