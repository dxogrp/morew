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

end MorewTest.Transform
