/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.Remove

/-! # Removed rows stay absent across imports and continued reformulations -/

namespace MorewTest.Reformulation.ImportedRemove

open Morew Remove
noncomputable section

reformulation continued : reused := by
  remove at last
  rename copied to domain
  substitute u := v
  conic

example : IsConic continued := continued.isConic
example : GlobalEquivalence bounded continued :=
  reused.equivalence.trans continued.equivalence

reformulation continuedCheckpoint : checkpointChain := by
  derive copied : Real.exp w ≤ 3 using (by intro point hp; exact hp.1)
  remove at copied
  rename domain_x to cap
  substitute w := z

example (z v t : ℝ) : continuedCheckpoint.feasible ((z, v), t) ↔
    Real.exp z ≤ 3 ∧ (Real.exp v ≤ 4 ∧ True) ∧ z + v ≤ t := Iff.rfl
example : GlobalEquivalence positive continuedCheckpoint :=
  checkpointChain.equivalence.trans continuedCheckpoint.equivalence

section
variable (offset : ℝ)

reformulation continuedFamily : (familyRemoved offset) := by
  derive copied : 0 ≤ shifted using (by intro point hp; exact hp)
  remove at bound
  rename copied to bound

example (x : ℝ) : (continuedFamily offset).feasible x ↔ 0 ≤ x + offset := Iff.rfl
example : GlobalEquivalence (family offset) (continuedFamily offset) :=
  (familyRemoved.equivalence offset).trans (continuedFamily.equivalence offset)
end

namespace Instances
set_option linter.overlappingInstances false
variable [first : Remove.Instances.Parameter] [second : Remove.Instances.Parameter]

reformulation continued : (@Remove.Instances.target first second) := by
  derive repeated : right ≤ x using (by intro point hp; exact hp.1)
  remove at copy
  substitute x := u

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``continued
    | Lean.throwError "missing imported captured-instance presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent `replayed) := $term))

example (u : ℝ) : (@replayed first second).objective u =
    @Remove.Instances.Parameter.value first + u := rfl
example (u : ℝ) : (@replayed first second).feasible u ↔
    u ≤ @Remove.Instances.Parameter.value first ∧ @Remove.Instances.Parameter.value second ≤ u :=
  Iff.rfl
end Instances

namespace Shadow
def cap (_ : ℝ) : Prop := False
def shifted (_ : ℝ) : ℝ := 100

reformulation hygienic : Hygiene.target := by
  derive copied : Remove.Hygiene.cap x using (by intro point hp; exact hp)
  remove at cap
  rename copied to cap

example (x : ℝ) : hygienic.feasible x ↔ Remove.Hygiene.cap x := Iff.rfl

run_cmd do
  for (original, copied) in #[
      (``shortened, `shortenedCopy), (``aliasRemoved, `groupedCopy),
      (``unconstrained, `emptyCopy), (``continuedCheckpoint, `checkpointCopy),
      (``hygienic, `hygienicCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported removal lost presentation metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "removed presentation replay contains incomplete evidence"

example : shortenedCopy = shortened := rfl
example : groupedCopy = aliasRemoved := rfl
example : emptyCopy = unconstrained := rfl
example : checkpointCopy = continuedCheckpoint := rfl
example : hygienicCopy = hygienic := rfl
end Shadow

run_cmd do
  for (name, expected) in #[
      (``continued, #[`domain, `upper]),
      (``continuedCheckpoint, #[`cap, `grouped, `objective_bound]),
      (``continuedFamily, #[`bound]),
      (``Shadow.hygienic, #[`cap])] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing imported removal presentation"
    unless view.constraints.map (·.name.eraseMacroScopes) == expected do
      Lean.throwError "imported removal changed ordered labels"

end
end MorewTest.Reformulation.ImportedRemove
