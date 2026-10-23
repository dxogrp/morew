import Morew.Conic
import Mathlib.Tactic.NormNum

/-!
# Exponential cones and exact finite representations

These semantic tests use the public conic entry point without installing the
surface language. Domain counterexamples record why totalized real formulas
must not be rewritten without the stated evidence.
-/

assert_not_exists Morew.ExactConstraintLift Morew.Syntax.ProblemView

namespace MorewTest.Conic.Exponential

open Morew Morew.Conic Morew.Conic.Exponential

noncomputable section

example (a t : ℝ) : Real.exp a ≤ t ↔ (a, 1, t) ∈ EXP := exp_le_iff a t

example (a t : ℝ) (ha : 0 < a) :
    t ≤ Real.log a ↔ (t, 1, a) ∈ EXP := le_log_iff a t ha

example (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    a * Real.log (a / b) ≤ t ↔ (-t, a, b) ∈ EXP :=
  relativeEntropy_le_iff a b t ha hb

example (b t : ℝ) (hb : 0 ≤ b) :
    Fn.relativeEntropy 0 b ≤ t ↔ (-t, 0, b) ∈ EXP :=
  relativeEntropy_zero_le_iff b t hb

example (t : ℝ) : Fn.relativeEntropy 0 0 ≤ t ↔ (-t, 0, 0) ∈ EXP :=
  relativeEntropy_zero_le_iff 0 t le_rfl

/-! Native totalization is not the usual logarithm/entropy domain. -/

example : (0 : ℝ) ≤ Real.log 0 := by simp
example : ¬ ((0 : ℝ), 1, 0) ∈ EXP := by norm_num
example : Fn.relativeEntropy 1 0 ≤ 0 := by simp [Fn.relativeEntropy]
example : ¬ (-(0 : ℝ), 1, 0) ∈ EXP := by norm_num
example : Fn.relativeEntropy 1 (-1) ≤ 0 := by simp [Fn.relativeEntropy]
example : ¬ (-(0 : ℝ), 1, -1) ∈ EXP := by norm_num

/-! Finite representations retain one grouped row and one scalar sum. -/

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
