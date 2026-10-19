import PTran.Core
import Mathlib.Data.Real.Basic

/-!
# Tests for the semantic core

These compile-time examples exercise the order-generic definitions directly,
without depending on the surface syntax or transformation framework.
-/

namespace PTranTest.Core

open PTran

/-! ## Minimization and maximization -/

def naturalMinimum : Problem Nat Nat where
  objective := fun n => n
  feasible := fun _ => True

def naturalZero : FeasiblePoint naturalMinimum := ⟨0, trivial⟩

theorem naturalZero_isGlobalOptimum :
    naturalMinimum.IsGlobalOptimum naturalZero := by
  intro y
  exact Nat.zero_le y.1

def boundedScore : Problem Nat Nat where
  objective := fun n => n
  feasible := fun n => n ≤ 3

/-- Reading the objective order dually turns the bounded score problem into a
maximization problem. -/
def naturalMaximum : Problem Nat (OrderDual Nat) := boundedScore.orderDual

def naturalThree : FeasiblePoint naturalMaximum := ⟨3, le_rfl⟩

theorem naturalThree_isGlobalOptimum :
    naturalMaximum.IsGlobalOptimum naturalThree := by
  intro y
  exact y.2

example : naturalMaximum.objective naturalThree.1 = (3 : OrderDual Nat) := rfl

/-! ## One-way improvements and global equivalences -/

def taggedMinimum : Problem (Nat × Unit) Nat where
  objective := fun x => x.1
  feasible := fun _ => True

def tagForward : GlobalImprovement naturalMinimum taggedMinimum where
  map := fun x => ⟨(x.1, ()), trivial⟩
  objective_le := fun _ => le_rfl

def tagBackward : GlobalImprovement taggedMinimum naturalMinimum where
  map := fun x => ⟨x.1.1, trivial⟩
  objective_le := fun _ => le_rfl

def tagEquivalence : GlobalEquivalence naturalMinimum taggedMinimum where
  forward := tagForward
  backward := tagBackward

def doublyTaggedMinimum : Problem ((Nat × Unit) × Unit) Nat where
  objective := fun x => x.1.1
  feasible := fun _ => True

def doubleTagForward : GlobalImprovement taggedMinimum doublyTaggedMinimum where
  map := fun x => ⟨(x.1, ()), trivial⟩
  objective_le := fun _ => le_rfl

def doubleTagBackward : GlobalImprovement doublyTaggedMinimum taggedMinimum where
  map := fun x => ⟨x.1.1, trivial⟩
  objective_le := fun _ => le_rfl

def doubleTagEquivalence :
    GlobalEquivalence taggedMinimum doublyTaggedMinimum where
  forward := doubleTagForward
  backward := doubleTagBackward

example : GlobalImprovement naturalMinimum naturalMinimum :=
  GlobalImprovement.refl naturalMinimum

example : GlobalImprovement naturalMinimum doublyTaggedMinimum :=
  tagForward.trans doubleTagForward

example : GlobalEquivalence naturalMinimum naturalMinimum :=
  GlobalEquivalence.refl naturalMinimum

example : GlobalEquivalence taggedMinimum naturalMinimum :=
  tagEquivalence.symm

example : GlobalEquivalence naturalMinimum doublyTaggedMinimum :=
  tagEquivalence.trans doubleTagEquivalence

example : GlobalImprovement naturalMinimum taggedMinimum :=
  tagEquivalence.toGlobalImprovement

/-! ## Preservation results -/

theorem naturalMinimum_hasFeasiblePoint : naturalMinimum.HasFeasiblePoint :=
  ⟨naturalZero⟩

example : taggedMinimum.HasFeasiblePoint :=
  tagForward.map_hasFeasiblePoint naturalMinimum_hasFeasiblePoint

example : naturalMinimum.HasFeasiblePoint ↔ taggedMinimum.HasFeasiblePoint :=
  tagEquivalence.hasFeasiblePoint_iff

def taggedZero : FeasiblePoint taggedMinimum := ⟨(0, ()), trivial⟩

theorem taggedZero_isGlobalOptimum :
    taggedMinimum.IsGlobalOptimum taggedZero := by
  intro y
  exact Nat.zero_le y.1.1

example : taggedMinimum.IsGlobalOptimum (tagForward.map naturalZero) :=
  tagEquivalence.map_isGlobalOptimum naturalZero_isGlobalOptimum

example : naturalMinimum.IsGlobalOptimum (tagBackward.map taggedZero) :=
  tagEquivalence.map_isGlobalOptimum_backward taggedZero_isGlobalOptimum

example : naturalMinimum.HasGlobalOptimum ↔ taggedMinimum.HasGlobalOptimum :=
  tagEquivalence.hasGlobalOptimum_iff

example :
    taggedMinimum.objective (tagForward.map naturalZero).1 =
      naturalMinimum.objective naturalZero.1 :=
  tagEquivalence.objective_eq_of_isGlobalOptimum naturalZero_isGlobalOptimum

example :
    naturalMinimum.objective naturalZero.1 =
      taggedMinimum.objective taggedZero.1 :=
  tagEquivalence.objective_eq_of_optima
    naturalZero_isGlobalOptimum taggedZero_isGlobalOptimum

theorem zero_isLowerBound : naturalMinimum.IsObjectiveLowerBound 0 := by
  intro x
  exact Nat.zero_le x.1

example : taggedMinimum.IsObjectiveLowerBound 0 :=
  (tagEquivalence.isObjectiveLowerBound_iff 0).mp zero_isLowerBound

example :
    naturalMinimum.IsObjectiveLowerBound 0 ↔
      taggedMinimum.IsObjectiveLowerBound 0 :=
  tagEquivalence.isObjectiveLowerBound_iff 0

/-! ## Unboundedness -/

example : ¬ naturalMinimum.IsUnbounded := by
  intro h
  obtain ⟨x, hx⟩ := h 0
  exact (Nat.not_lt_zero x.1) hx

def integerLine : Problem Int Int where
  objective := fun x => x
  feasible := fun _ => True

def taggedIntegerLine : Problem (Int × Unit) Int where
  objective := fun x => x.1
  feasible := fun _ => True

def integerLineEquivalence : GlobalEquivalence integerLine taggedIntegerLine where
  forward := {
    map := fun x => ⟨(x.1, ()), trivial⟩
    objective_le := fun _ => le_rfl
  }
  backward := {
    map := fun x => ⟨x.1.1, trivial⟩
    objective_le := fun _ => le_rfl
  }

theorem integerLine_isUnbounded : integerLine.IsUnbounded := by
  intro bound
  exact ⟨⟨bound - 1, trivial⟩, sub_one_lt bound⟩

example : taggedIntegerLine.IsUnbounded :=
  integerLineEquivalence.forward.map_isUnbounded integerLine_isUnbounded

example : integerLine.IsUnbounded ↔ taggedIntegerLine.IsUnbounded :=
  integerLineEquivalence.isUnbounded_iff

/-! ## A nonconvex objective -/

/-- The double-well quartic is nonconvex on `ℝ`; the semantic core accepts it
without asking for, or storing, any convexity evidence. -/
def doubleWell : Problem ℝ ℝ where
  objective := fun x => (x ^ 2 - 1) ^ 2
  feasible := fun _ => True

def doubleWellOne : FeasiblePoint doubleWell := ⟨1, trivial⟩

theorem doubleWellOne_isGlobalOptimum :
    doubleWell.IsGlobalOptimum doubleWellOne := by
  intro y
  rw [show doubleWell.objective doubleWellOne.1 = 0 by
    simp [doubleWell, doubleWellOne]]
  change 0 ≤ (y.1 ^ 2 - 1) ^ 2
  exact sq_nonneg (y.1 ^ 2 - 1)

example : GlobalEquivalence doubleWell doubleWell :=
  GlobalEquivalence.refl doubleWell

example : doubleWell.HasGlobalOptimum :=
  ⟨doubleWellOne, doubleWellOne_isGlobalOptimum⟩

end PTranTest.Core
