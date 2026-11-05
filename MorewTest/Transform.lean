/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform
import Mathlib.Data.Real.Basic

/-!
# Tests for primitive verified transformations
-/

namespace MorewTest.Transform

open Morew

def squareProblem : Problem ℤ ℤ where
  objective x := x ^ 2
  feasible _ := True

def identityCoverage : FeasibleSurjection squareProblem (fun x : ℤ => x) where
  preimage x := x.1
  rightInverse _ := rfl

example :
    GlobalEquiv squareProblem
      (squareProblem.pullback fun x : ℤ => x) :=
  pullbackEquiv squareProblem (fun x : ℤ => x) identityCoverage

def squareEpigraph := squareProblem.epigraph

example : GlobalEquiv squareProblem squareEpigraph :=
  epigraphEquiv squareProblem

example (x : FeasiblePoint squareProblem) :
    (epigraphEquiv squareProblem).forward.map x =
      ⟨(x.1, squareProblem.objective x.1), x.2, le_rfl⟩ := rfl

/-- The epigraph theorem is independent of convexity. -/
def doubleWell : Problem ℝ ℝ where
  objective x := (x ^ 2 - 1) ^ 2
  feasible _ := True

example : GlobalEquiv doubleWell doubleWell.epigraph :=
  epigraphEquiv doubleWell

def boundedScore : Problem ℕ (OrderDual ℕ) where
  objective n := n
  feasible n := n ≤ 10

def scoreHypograph := boundedScore.hypograph

example : GlobalEquiv boundedScore scoreHypograph :=
  hypographEquiv (V := ℕ) boundedScore

/-- This target is exact only under the stronger retained bound. -/
def conditionalProblem : Problem ℕ ℕ where
  objective x := x
  feasible x := x ≤ 3 ∧ x ≤ 5

def conditionalDecomposition : ConstraintDecomposition conditionalProblem (· ≤ 5) where
  remainder x := x ≤ 3
  feasible_iff _ := Iff.rfl

private theorem conditionalExact (x : ℕ) (retained : x ≤ 3) :
    x ≤ 5 ↔ ∃ a : ℕ, a = x :=
  ⟨fun _ => ⟨x, rfl⟩, fun _ => retained.trans (by decide)⟩

noncomputable example : GlobalEquiv conditionalProblem
    (conditionalProblem.liftConstraintConditional conditionalDecomposition (fun x a : ℕ => a = x)) :=
  conditionalConstraintLiftEquivalence conditionalProblem conditionalDecomposition
    (fun x a : ℕ => a = x) conditionalExact

example : ¬ (∀ x : ℕ, x ≤ 5 ↔ ∃ a : ℕ, a = x) := by
  intro h
  have impossible := (h 6).mpr ⟨6, rfl⟩
  exact (by decide : ¬ 6 ≤ 5) impossible

/-- An infeasible retained constraint permits an empty auxiliary type. -/
def impossibleProblem : Problem ℕ ℕ where
  objective x := x
  feasible _ := False ∧ True

def impossibleDecomposition : ConstraintDecomposition impossibleProblem (fun _ => True) where
  remainder _ := False
  feasible_iff _ := Iff.rfl

noncomputable example : GlobalEquiv impossibleProblem
    (impossibleProblem.liftConstraintConditional impossibleDecomposition
      (fun (_ : ℕ) (_ : Empty) => True)) :=
  conditionalConstraintLiftEquivalence impossibleProblem impossibleDecomposition
    (fun (_ : ℕ) (_ : Empty) => True) (fun _ h => h.elim)

end MorewTest.Transform
