/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew
import MorewTest.Diagnostics

/-!
# Custom exact certificates with second-order targets

Every supported certificate family can emit cone membership rows. Nested
conjunctions and local aliases preserve row order, and auxiliary coordinates
extend the original decision domain once.
-/

namespace MorewTest.Reformulation.SecondOrderCustom

open Morew Morew.Conic

noncomputable section

private theorem scalarCone (t : ℝ) :
    (t, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier ↔ 0 ≤ t := by
  change ‖(0 : EuclideanSpace ℝ (Fin 0))‖ ≤ t ↔ 0 ≤ t
  simp

def userIdentity (x : ℝ) : ℝ := x

def userSquare (x : ℝ) : ℝ := x ^ 2

def graphRule : GraphRepresentation userIdentity where
  Auxiliary := Unit
  target x y _ :=
    let difference := y - x
    True ∧ (difference, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier ∧
      ((x - y, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier ∧ True)
  source_iff_exists x y := by
    simp only [userIdentity, scalarCone, sub_nonneg, and_true, true_and, exists_const]
    exact eq_comm.trans le_antisymm_iff

def epigraphRule : EpigraphRepresentation userSquare where
  Auxiliary := Unit
  target x t _ := (t, 1 / 2, ![x]) ∈ (Cone.rotatedSecondOrder 1).carrier
  source_iff_exists x t := by
    simpa only [userSquare, exists_const] using SecondOrder.square_le_iff x t

def hypographRule : HypographRepresentation userIdentity where
  Auxiliary := Unit
  target x t _ := (x - t, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier
  source_iff_exists x t := by
    simp only [userIdentity, scalarCone, sub_nonneg, exists_const]

def auxiliaryRule : ExactConstraintLift
    (fun point : ℝ × ℝ => userSquare point.1 ≤ point.2) where
  Auxiliary := ℝ
  target point u := u = point.1 ∧
    (let bound := point.2
     True ∧ (bound, 1 / 2, ![u]) ∈ (Cone.rotatedSecondOrder 1).carrier)
  source_iff_exists point := by
    simp only [true_and, exists_eq_left, userSquare]
    exact SecondOrder.square_le_iff point.1 point.2

def graphSource :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      graph : y = userIdentity x

reformulation graphTarget : graphSource := by
  conic at graph using graphRule

example : GlobalEquivalence graphSource graphTarget := graphTarget.equivalence

example (x y : ℝ) : graphTarget.feasible (x, y) ↔
    (y - x, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier ∧
      (x - y, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier := Iff.rfl

def epigraphSource :=
  problem (x y : ℝ)
    minimize y
    subject to
      epi_row : userSquare x ≤ y

reformulation epigraphTarget : epigraphSource := by
  conic at epi_row using epigraphRule

example : GlobalEquivalence epigraphSource epigraphTarget := epigraphTarget.equivalence

example (x y : ℝ) : epigraphTarget.feasible (x, y) ↔
    (y, 1 / 2, ![x]) ∈ (Cone.rotatedSecondOrder 1).carrier := Iff.rfl

def hypographSource :=
  problem (x y : ℝ)
    minimize x
    subject to
      hypo_row : y ≤ userIdentity x

reformulation hypographTarget : hypographSource := by
  conic at hypo_row using hypographRule

example : GlobalEquivalence hypographSource hypographTarget := hypographTarget.equivalence

example (x y : ℝ) : hypographTarget.feasible (x, y) ↔
    (x - y, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier := Iff.rfl

def source :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      before : Real.exp x ≤ 100
      auxiliary : userSquare x ≤ y
      after : y ≤ 10

reformulation target : source := by
  conic at auxiliary using auxiliaryRule

example : GlobalEquivalence source target := target.equivalence

example (x y u : ℝ) : target.objective ((x, y), u) = x + y := rfl

example (x y u : ℝ) : target.feasible ((x, y), u) ↔
    Real.exp x ≤ 100 ∧
      u = x ∧ (y, 1 / 2, ![u]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧ y ≤ 10 := Iff.rfl

-- Keep the complete chain at the default heartbeat limit: serializing each
-- primitive's proof data inline used to exceed that limit at declaration time.
def combinedSource :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      before : Real.exp x ≤ 100
      graph : y = userIdentity x
      epi_row : userSquare x ≤ y
      hypo_row : y ≤ userIdentity x
      auxiliary : userSquare x ≤ y
      after : y ≤ 10

reformulation combinedTarget : combinedSource := by
  conic at graph using graphRule
  conic at epi_row using epigraphRule
  conic at hypo_row using hypographRule
  conic at auxiliary using auxiliaryRule

example : GlobalEquivalence combinedSource combinedTarget := combinedTarget.equivalence

example (x y u : ℝ) : combinedTarget.feasible ((x, y), u) ↔
    Real.exp x ≤ 100 ∧
      (y - x, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier ∧
      (x - y, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier ∧
      (y, 1 / 2, ![x]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      (x - y, (0 : Fin 0 → ℝ)) ∈ (Cone.secondOrder 0).carrier ∧
      u = x ∧ (y, 1 / 2, ![u]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧ y ≤ 10 := Iff.rfl

elab "assert_atomic_reformulation% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  for (name, _) in after.constants.toList do
    unless before.contains name do
      Lean.throwError "failed reformulation leaked auxiliary declaration {name}"

#guard_error_fragments ["constraint `after`: the exact representation input is not the decision space"] in
assert_atomic_reformulation%
reformulation wrongSource : source certificate wrongSourceAlias := by
  conic at auxiliary using auxiliaryRule
  conic at after using auxiliaryRule

def nonlinearSource :=
  problem (x y : ℝ)
    minimize y
    subject to
      bad : userSquare (x * x) ≤ y

/-- error: constraint `bad`: generated row -/
#guard_msgs (substring := true) in
reformulation nonaffineTarget : nonlinearSource certificate nonaffineTargetAlias := by
  conic at bad using epigraphRule

run_cmd do
  let env ← Lean.getEnv
  for name in #[`wrongSource, `nonaffineTarget] do
    let full := `MorewTest.Reformulation.SecondOrderCustom ++ name
    for declaration in #[full, full ++ `equivalence,
        `MorewTest.Reformulation.SecondOrderCustom ++
          Lean.Name.mkSimple (name.toString ++ "Alias")] do
      if env.contains declaration then
        Lean.throwError "failed custom rewrite emitted {declaration}"
    if (Morew.Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed custom rewrite registered presentation metadata"

end
end MorewTest.Reformulation.SecondOrderCustom
