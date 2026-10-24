import Morew.Reformulation.Command

/-!
# Structure defaults preserve explicit occurrences

Replay must retain explicitly supplied fields even when they reduce to a
structure default. Ambient pretty-printing options cannot change selection.
-/

namespace MorewTest.Reformulation.OccurrenceStructureDefaults

open Morew
noncomputable section

structure Box where
  value : ℝ := 0

def source :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize (Box.mk ((fun _ : ℝ => (0 : ℝ)) loss)).value
    subject to
      cap : (Box.mk ((fun _ : ℝ => (0 : ℝ)) loss)).value ≤ 1

set_option pp.structureInstances.defaults false in
reformulation lifted : source := by
  epigraph t at loss

example : GlobalEquivalence source lifted := lifted.equivalence
example (x t : ℝ) : lifted.objective (x, t) = 0 := rfl
example (x t : ℝ) : lifted.feasible (x, t) ↔ (0 : ℝ) ≤ 1 ∧ x ^ 2 ≤ t := Iff.rfl

-- The untouched row retains its explicit field across a generated declaration.
set_option pp.structureInstances.defaults false in
reformulation continued : lifted := by
  epigraph s at loss in cap

example : GlobalEquivalence lifted continued := continued.equivalence
example (x t s : ℝ) : continued.feasible ((x, t), s) ↔
    (0 : ℝ) ≤ 1 ∧ x ^ 2 ≤ t ∧ x ^ 2 ≤ s := Iff.rfl

-- Typed expression selection must see the same retained field.
reformulation expressionLift : source := by
  epigraph t at ((fun _ : ℝ => (0 : ℝ)) loss)

example : GlobalEquivalence source expressionLift := expressionLift.equivalence
example (x t : ℝ) : expressionLift.objective (x, t) = t := rfl
example (x t : ℝ) : expressionLift.feasible (x, t) ↔
    (0 : ℝ) ≤ 1 ∧ 0 ≤ t := Iff.rfl

def repeated :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize (Box.mk ((fun _ : ℝ => (0 : ℝ)) loss)).value + loss

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedLift : repeated := by
  epigraph t at loss

run_cmd do
  if (← Lean.getEnv).contains `MorewTest.Reformulation.OccurrenceStructureDefaults.repeatedLift then
    Lean.throwError "ambiguous structure-field selection emitted a declaration"

end
end MorewTest.Reformulation.OccurrenceStructureDefaults
