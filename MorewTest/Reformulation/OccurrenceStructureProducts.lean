/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Command

/-!
# Product binders preserve direct occurrence structure

Recovering an applied problem removes its generated product destructuring while
retaining user lambdas, projections, and matches in objectives and constraints.
-/

namespace MorewTest.Reformulation.OccurrenceStructureProducts

open Morew
noncomputable section

def twoFamily (offset : ℝ) :=
  problem (x y : ℝ)
    minimize (fun u : ℝ => u + u) ((x - offset) ^ 2) + y

reformulation twoLift : (twoFamily 2) := by
  epigraph t at ((x - 2) ^ 2)

example : GlobalEquivalence (twoFamily 2) twoLift := twoLift.equivalence
example (x y t : ℝ) : twoLift.objective ((x, y), t) = (t + t) + y := rfl
example (x y t : ℝ) : twoLift.feasible ((x, y), t) ↔ (x - 2) ^ 2 ≤ t := Iff.rfl

def threeFamily (offset : ℝ) :=
  problem (x y z : ℝ)
    minimize (fun u : ℝ => u + u) ((x - offset) ^ 2) + y + z
    subject to
      cap : (fun u : ℝ => u + u ≤ 20) (y ^ 2)

reformulation threeLift : (threeFamily 2) := by
  epigraph t at ((x - 2) ^ 2)

example : GlobalEquivalence (threeFamily 2) threeLift := threeLift.equivalence
example (x y z t : ℝ) : threeLift.objective (((x, y), z), t) =
    (t + t) + y + z := rfl
example (x y z t : ℝ) : threeLift.feasible (((x, y), z), t) ↔
    y ^ 2 + y ^ 2 ≤ 20 ∧ (x - 2) ^ 2 ≤ t := Iff.rfl

reformulation threeCapLift : (threeFamily 2) := by
  epigraph t at (y ^ 2) in cap

example : GlobalEquivalence (threeFamily 2) threeCapLift := threeCapLift.equivalence
example (x y z t : ℝ) : threeCapLift.objective (((x, y), z), t) =
    ((x - 2) ^ 2 + (x - 2) ^ 2) + y + z := rfl
example (x y z t : ℝ) : threeCapLift.feasible (((x, y), z), t) ↔
    t + t ≤ 20 ∧ y ^ 2 ≤ t := Iff.rfl

-- A projection written by the user still contains both direct references.
def repeatedProjection :=
  problem (x y : ℝ)
    let loss := x ^ 2
    minimize (loss, loss).1 + y

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedProjectionLift : repeatedProjection := by
  epigraph t at loss

-- The same boundary applies to a user match inside an applied source.
def repeatedMatch (offset : ℝ) :=
  problem (x y : ℝ)
    minimize (match ((x - offset) ^ 2, (x - offset) ^ 2) with
      | (a, _b) => a) + y

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedMatchLift : (repeatedMatch 2) := by
  epigraph t at ((x - 2) ^ 2)

-- One pair-valued decision is not two decision binders.
def pairFamily (offset : ℝ) :=
  problem (p : ℝ × ℝ)
    minimize (fun u : ℝ => u + u) ((p.1 - offset) ^ 2) + p.2

reformulation pairLift : (pairFamily 2) := by
  epigraph t at ((p.1 - 2) ^ 2)

example : GlobalEquivalence (pairFamily 2) pairLift := pairLift.equivalence
example (p : ℝ × ℝ) (t : ℝ) : pairLift.objective (p, t) = (t + t) + p.2 := rfl
example (p : ℝ × ℝ) (t : ℝ) : pairLift.feasible (p, t) ↔
    (p.1 - 2) ^ 2 ≤ t := Iff.rfl

def pairMatch (offset : ℝ) :=
  problem (p : ℝ × ℝ)
    minimize match p with
      | (x, _y) => (x - offset) ^ 2

-- The branch variable is not a direct occurrence of the decision projection.
/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation pairMatchLift : (pairMatch 2) := by
  epigraph t at ((p.1 - 2) ^ 2)

-- Substituting a lambda parameter must not duplicate its argument first.
def functionFamily (f : ℝ → ℝ) :=
  problem (x y : ℝ)
    minimize f (x ^ 2) + y

reformulation functionLift : (functionFamily (fun u => u + u)) := by
  epigraph t at (x ^ 2)

example : GlobalEquivalence (functionFamily (fun u => u + u)) functionLift :=
  functionLift.equivalence
example (x y t : ℝ) : functionLift.objective ((x, y), t) = (t + t) + y := rfl
example (x y t : ℝ) : functionLift.feasible ((x, y), t) ↔ x ^ 2 ≤ t := Iff.rfl

end
end MorewTest.Reformulation.OccurrenceStructureProducts
