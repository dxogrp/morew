/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.RenameBackends

/-! # Renamed labels and exact presentation replay survive module imports -/

namespace MorewTest.Reformulation.ImportedRename

open Morew Rename
noncomputable section

reformulation continued : conicRows := by
  rename upper to imported_upper
  conic at imported_upper using upperLift
  rename imported_upper_conic_1 to final_upper

example : continued = conicRows := rfl
example : GlobalEquivalence absoluteSource continued :=
  conicRows.equivalence.trans continued.equivalence

reformulation renamedAgain : ordered := by
  rename bounds.upper to cap
  rename lower to first

example : renamedAgain = orderedSource := rfl

section
variable (offset : ℝ)

reformulation continuedFamily : (renamedFamily offset) := by
  rename domain to shifted_lower
  derive copied : 0 ≤ shifted using (by intro point hp; exact hp)

example (x : ℝ) : (continuedFamily offset).feasible x ↔
    0 ≤ x + offset ∧ 0 ≤ x + offset := Iff.rfl
example : GlobalEquivalence (family offset) (continuedFamily offset) :=
  (renamedFamily.equivalence offset).trans (continuedFamily.equivalence offset)
end

namespace Instances

set_option linter.overlappingInstances false
variable [first : Rename.Instances.Parameter] [second : Rename.Instances.Parameter]

reformulation continued : (@Rename.Instances.target first second) := by
  rename interval to preserved
  substitute x := u

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``continued
    | Lean.throwError "missing imported instance presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (u : ℝ) : (@replayed first second).objective u =
    @Rename.Instances.Parameter.value first + u := rfl
example (u : ℝ) : (@replayed first second).feasible u ↔
    @Rename.Instances.Parameter.value second ≤ u ∧
      u ≤ @Rename.Instances.Parameter.value first := Iff.rfl

reformulation continuedBound : (@Rename.Instances.bounded first second) := by
  rename bound to objective_bound
  substitute u := v

example (v t : ℝ) : (@continuedBound first second).feasible (v, t) ↔
    (@Rename.Instances.Parameter.value second ≤ v ∧
      v ≤ @Rename.Instances.Parameter.value first) ∧
      @Rename.Instances.Parameter.value first + v ≤ t := Iff.rfl

end Instances

namespace Shadow

def shifted (_ : ℝ) : ℝ := 100
def Positive (_ : ℝ) : Prop := False
def cap (_ : ℝ) : Prop := False

reformulation hygienic : Hygiene.target := by
  rename bound to cap
  substitute x := u

example (u : ℝ) : hygienic.feasible u ↔ Rename.Hygiene.cap u := Iff.rfl
example : GlobalEquivalence Hygiene.source hygienic :=
  Hygiene.target.equivalence.trans hygienic.equivalence

run_cmd do
  for (original, copied) in #[
      (``ordered, `orderedCopy), (``grouped, `groupedCopy),
      (``renamedAgain, `renamedCopy), (``principalBound, `branchCopy),
      (``hygienic, `hygienicCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported rename lost presentation metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "renamed presentation replay contains incomplete evidence"

example : orderedCopy = ordered := rfl
example : groupedCopy = grouped := rfl
example : renamedCopy = renamedAgain := rfl
example : branchCopy = principalBound := rfl
example : hygienicCopy = hygienic := rfl

end Shadow

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``continued
    | Lean.throwError "missing imported generated-row presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`before, `final_upper, `cap_conic_2, `after] do
    Lean.throwError "imported rename changed row order or generated-family labels"

end
end MorewTest.Reformulation.ImportedRename
