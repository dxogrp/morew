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
    GlobalEquivalence squareProblem
      (squareProblem.pullback fun x : ℤ => x) :=
  pullbackEquivalence squareProblem (fun x : ℤ => x) identityCoverage

def squareEpigraph := squareProblem.epigraph

example : GlobalEquivalence squareProblem squareEpigraph :=
  epigraphEquivalence squareProblem

example (x : FeasiblePoint squareProblem) :
    (epigraphEquivalence squareProblem).forward.map x =
      ⟨(x.1, squareProblem.objective x.1), x.2, le_rfl⟩ := rfl

/-- The epigraph theorem is independent of convexity. -/
def doubleWell : Problem ℝ ℝ where
  objective x := (x ^ 2 - 1) ^ 2
  feasible _ := True

example : GlobalEquivalence doubleWell doubleWell.epigraph :=
  epigraphEquivalence doubleWell

def boundedScore : Problem ℕ (OrderDual ℕ) where
  objective n := n
  feasible n := n ≤ 10

def scoreHypograph := boundedScore.hypograph

example : GlobalEquivalence boundedScore scoreHypograph :=
  hypographEquivalence (V := ℕ) boundedScore

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

noncomputable example : GlobalEquivalence conditionalProblem
    (conditionalProblem.liftConstraintConditional conditionalDecomposition (fun x a : ℕ => a = x)) :=
  conditionalConstraintLiftEquivalence conditionalProblem conditionalDecomposition
    (fun x a : ℕ => a = x) conditionalExact

example : ¬ (∀ x : ℕ, x ≤ 5 ↔ ∃ a : ℕ, a = x) := by
  intro h
  have impossible := (h 6).mpr ⟨6, rfl⟩
  exact (by decide : ¬ 6 ≤ 5) impossible

/-- A false retained context needs neither an inhabited auxiliary type nor a
global witness outside the feasible set. -/
def impossibleProblem : Problem ℕ ℕ where
  objective x := x
  feasible _ := False ∧ True

def impossibleDecomposition : ConstraintDecomposition impossibleProblem (fun _ => True) where
  remainder _ := False
  feasible_iff _ := Iff.rfl

noncomputable example : GlobalEquivalence impossibleProblem
    (impossibleProblem.liftConstraintConditional impossibleDecomposition
      (fun (_ : ℕ) (_ : Empty) => True)) :=
  conditionalConstraintLiftEquivalence impossibleProblem impossibleDecomposition
    (fun (_ : ℕ) (_ : Empty) => True) (fun _ h => h.elim)

end MorewTest.Transform
