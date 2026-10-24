/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.LocalDefinitionRecovery.Defined

/-!
# Recovery through source containers

Source reduction must cross enclosing lets and irreducible declarations while
retaining the identities of equal-valued model-local definitions.
-/

namespace MorewTest.Reformulation.LocalDefinitionRecovery

open Morew
noncomputable section

reformulation surroundingWhole : Defined.surrounding := by
  epigraph t

example : GlobalEquivalence Defined.surrounding surroundingWhole :=
  surroundingWhole.equivalence
example (x t : ℝ) : surroundingWhole.feasible (x, t) ↔
    (x + 2) + (x + 2) ≤ t := Iff.rfl

reformulation surroundingNamed : Defined.surrounding := by
  epigraph t at loss

example (x t : ℝ) : surroundingNamed.objective (x, t) = t + (x + 2) := rfl
example (x t : ℝ) : surroundingNamed.feasible (x, t) ↔ x + 2 ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  let loss := x + 2
  let same := x + 2
  let unused := x - 2
  minimize t + same
  subject to
    epigraph_t : loss ≤ t
-/
#guard_msgs in
#printp surroundingNamed

reformulation irreducibleWhole : Defined.irreducible := by
  epigraph t

example : GlobalEquivalence Defined.irreducible irreducibleWhole :=
  irreducibleWhole.equivalence
example (x t : ℝ) : irreducibleWhole.feasible (x, t) ↔
    (x + 2) + (x + 2) ≤ t := Iff.rfl

reformulation irreducibleNamed : Defined.irreducible := by
  epigraph t at loss

/--
info: problem (x t : ℝ)
  let loss := x + 2
  let same := x + 2
  minimize t + same
  subject to
    epigraph_t : loss ≤ t
-/
#guard_msgs in
#printp irreducibleNamed

section

variable (offset : ℝ)

reformulation appliedWhole : (Defined.family offset) := by
  epigraph t

reformulation appliedNamed : (Defined.family offset) := by
  epigraph t at loss

end

example (offset x t : ℝ) : (appliedWhole offset).feasible (x, t) ↔
    (x + (offset + 1)) + (x + (offset + 1)) ≤ t := Iff.rfl
example (offset x t : ℝ) : (appliedNamed offset).objective (x, t) =
    t + (x + (offset + 1)) := rfl

reformulation continued : (appliedNamed 2) := by
  epigraph s at same

example (x t s : ℝ) : continued.objective ((x, t), s) = t + s := rfl
example (x t s : ℝ) : continued.feasible ((x, t), s) ↔
    x + (2 + 1) ≤ t ∧ x + (2 + 1) ≤ s := Iff.rfl

universe u

section

variable (α : Type u) [Preorder α] (witness : True)

reformulation genericWhole : (Defined.generic α witness) := by
  epigraph a

example (x a : α) : (genericWhole α witness).feasible (x, a) ↔ x ≤ a := Iff.rfl

end

run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo ``genericWhole
  unless info.levelParams.length == 1 do
    Lean.throwError "source-container recovery lost its universe parameter"
  Lean.Meta.forallTelescope info.type fun parameters _ => do
    unless parameters.size == 3 do
      Lean.throwError "source-container recovery lost its proof or instance parameter"

end
end MorewTest.Reformulation.LocalDefinitionRecovery
