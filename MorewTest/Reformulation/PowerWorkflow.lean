/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics

/-!
# Power endpoints, ambiguity, and explicit lifting workflows

Terminal affine certification preserves endpoint expressions. Targeted commands
continue to require a unique registered replacement, even for affine endpoints.
-/

namespace MorewTest.Reformulation.PowerWorkflow

open Morew Morew.Conic

noncomputable section

namespace Endpoints

def source :=
  problem (x t : ℝ)
    minimize Real.rpow (Real.sin x) 0 + x ^ (1 : ℝ)
    subject to
      bound : Real.rpow x 0 ≤ t
      lower : -2 ≤ x

reformulation targeted : source := by
  conic at bound

reformulation ready : source := by
  conic

example : GlobalEquivalence source targeted := targeted.equivalence
example : GlobalEquivalence source ready := ready.equivalence
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents
example (x t : ℝ) : targeted.feasible (x, t) ↔ 1 ≤ t ∧ -2 ≤ x := Iff.rfl
example (x t : ℝ) : ready.feasible (x, t) ↔
    t - Real.rpow x 0 ∈ ℝ₊ ∧ x + 2 ∈ ℝ₊ := Iff.rfl
example : ready.objective = source.objective := rfl
example : ready.feasible (-1, 1) := by
  change 0 ≤ 1 - (-1 : ℝ) ^ (0 : ℝ) ∧ 0 ≤ -1 + (2 : ℝ)
  norm_num

def overlapping :=
  problem (x y : ℝ)
    maximize y
    subject to bound : Real.rpow x 0 ≤ Real.rpow y 1

#guard_error_fragments ["ambiguous exact conic rules", "Morew.Conic.Power.rpowOneHypograph",
    "Morew.Conic.Power.rpowZeroEpigraph", "using"] in
reformulation ambiguous : overlapping := by
  conic at bound

assert_not_exists ambiguous ambiguous.equivalence

reformulation chooseLeft : overlapping := by
  conic at bound using Conic.Power.rpowZeroEpigraph

reformulation chooseRight : overlapping := by
  conic at bound using Conic.Power.rpowOneHypograph

-- Direct affine certification takes precedence over registry ambiguity.
reformulation overlapReady : overlapping := by
  conic

example : GlobalEquivalence overlapping chooseLeft := chooseLeft.equivalence
example : GlobalEquivalence overlapping chooseRight := chooseRight.equivalence
example : overlapReady.conicForm.data.sense = .maximize := rfl

end Endpoints

namespace Nested

def source :=
  problem (x y : ℝ)
    let cost := Real.rpow x (3 / 2)
    let sameCost := Real.rpow x (3 / 2)
    minimize y
    subject to
      domain : 0 ≤ x
      budget : cost + y ≤ 10
      untouched : sameCost ≤ 20

-- Lift the nested occurrence first; the generated whole bound is selectable.
reformulation lifted : source := by
  epigraph a at cost in budget as powerBound
  conic at powerBound

reformulation ready : lifted := by
  conic

example : GlobalEquivalence source lifted := lifted.equivalence
example : GlobalEquivalence lifted ready := ready.equivalence
example : Conic.Form ready := ready.conicForm
example (x y a : ℝ) : lifted.feasible ((x, y), a) ↔
    0 ≤ x ∧ a + y ≤ 10 ∧ Real.rpow x (3 / 2) ≤ 20 ∧
      (a, 1, x) ∈ POW (1 / (3 / 2)) := Iff.rfl
example (x y a : ℝ) : lifted.objective ((x, y), a) = y := rfl

end Nested

namespace Names

def source :=
  problem (x t bound_aux : ℝ)
    maximize t
    subject to
      domain : 0 ≤ x
      bound_conic_1 : bound_aux = x
      bound : t ≤ Real.rpow x (1 / 2)

reformulation target : source := by
  conic at bound

example : GlobalEquivalence source target := target.equivalence
example (x t previous u : ℝ) : target.feasible (((x, t), previous), u) ↔
    0 ≤ x ∧ previous = x ∧ 0 ≤ u ∧ t ≤ u ∧ (x, 1, u) ∈ POW (1 / 2) := Iff.rfl
example (x t previous u : ℝ) : target.objective (((x, t), previous), u) = t := rfl

-- The old row and coordinate retain their names; generated names are unique.
run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing collision-test presentation"
  unless view.binders.size == 4 && view.constraints.size == 5 do
    Lean.throwError "unexpected power auxiliary or generated row count"
  unless view.binders[2]!.name.eraseMacroScopes == `bound_aux &&
      view.binders[3]!.name.eraseMacroScopes != `bound_aux &&
      view.constraints[1]!.name.eraseMacroScopes == `bound_conic_1 do
    Lean.throwError "power rewrite did not preserve existing names"
  let names := view.constraints.map (·.name.eraseMacroScopes)
  unless names.toList.eraseDups.length == names.size do
    Lean.throwError "power rewrite reused a constraint label"

end Names

end
end MorewTest.Reformulation.PowerWorkflow
