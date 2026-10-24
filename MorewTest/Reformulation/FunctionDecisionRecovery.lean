/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.FunctionDecisionRecovery.Defined

/-!
# Recovery of applied function-valued decisions

Decision projections in application heads must recover their binding identities
without losing arguments or erasing projections authored inside the model.
-/

namespace MorewTest.Reformulation.FunctionDecisionRecovery

open Morew Defined
noncomputable section

/--
info: problem (z : ℝ) (f : ℝ → ℝ)
  let unused := z
  minimize f z
  subject to
    budget : f z + z ≤ 10
-/
#guard_msgs in
#printp source

reformulation objectiveLift : source := by
  epigraph t at (f z)

example : GlobalEquivalence source objectiveLift := objectiveLift.equivalence
example (z t : ℝ) (f : ℝ → ℝ) : objectiveLift.objective ((z, f), t) = t := rfl
example (z t : ℝ) (f : ℝ → ℝ) : objectiveLift.feasible ((z, f), t) ↔
    f z + z ≤ 10 ∧ f z ≤ t := Iff.rfl

/--
info: problem (z : ℝ) (f : ℝ → ℝ) (t : ℝ)
  let unused := z
  minimize t
  subject to
    budget : f z + z ≤ 10
    epigraph_t : f z ≤ t
-/
#guard_msgs in
#printp objectiveLift

-- Both the imported generated source and the selected constraint are recovered.
reformulation constraintLift : generated := by
  epigraph t at (f z) in budget

example : GlobalEquivalence generated constraintLift := constraintLift.equivalence
example (z t : ℝ) (f : ℝ → ℝ) : constraintLift.objective ((z, f), t) = f z := rfl
example (z t : ℝ) (f : ℝ → ℝ) : constraintLift.feasible ((z, f), t) ↔
    t + z ≤ 10 ∧ f z ≤ t := Iff.rfl

section

variable (offset : ℝ)

-- A middle decision in a larger product has two explicit application arguments.
reformulation appliedNamed : (family offset) := by
  epigraph t at loss

reformulation appliedConstraint : (appliedNamed offset) := by
  epigraph s at (f x y) in budget

example : GlobalEquivalence (family offset) (appliedNamed offset) :=
  appliedNamed.equivalence offset
example (x y t s : ℝ) (f : ℝ → ℝ → ℝ) :
    (appliedConstraint offset).objective ((((x, f), y), t), s) = t + offset := rfl
example (x y t s : ℝ) (f : ℝ → ℝ → ℝ) :
    (appliedConstraint offset).feasible ((((x, f), y), t), s) ↔
      s ≤ 10 ∧ f x y ≤ t ∧ f x y ≤ s := Iff.rfl

end

def firstFunction :=
  problem (f : ℝ → ℝ → ℝ) (x y : ℝ)
    let unused := x
    minimize f x y

reformulation firstFunctionLift : firstFunction := by
  epigraph t at (f x y)

example : GlobalEquivalence firstFunction firstFunctionLift := firstFunctionLift.equivalence
example (x y t : ℝ) (f : ℝ → ℝ → ℝ) :
    firstFunctionLift.feasible (((f, x), y), t) ↔ f x y ≤ t := Iff.rfl

-- A projection inside the user's expression must survive decision recovery.
def projectedFunction :=
  problem (x : ℝ) (pair : (ℝ → ℝ) × ℝ)
    let unused := x
    minimize pair.1 x + pair.2

reformulation projectedFunctionLift : projectedFunction := by
  epigraph t at (pair.1 x)

example : GlobalEquivalence projectedFunction projectedFunctionLift :=
  projectedFunctionLift.equivalence
example (x t : ℝ) (pair : (ℝ → ℝ) × ℝ) :
    projectedFunctionLift.objective ((x, pair), t) = t + pair.2 := rfl
example (x t : ℝ) (pair : (ℝ → ℝ) × ℝ) :
    projectedFunctionLift.feasible ((x, pair), t) ↔ pair.1 x ≤ t := Iff.rfl

end
end MorewTest.Reformulation.FunctionDecisionRecovery
