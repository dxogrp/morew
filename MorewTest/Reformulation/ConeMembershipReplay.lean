/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.ConeMembership.Defined

/-!
# Exact replay independently of the later elaboration context

Generated metadata keeps its checked operations when new local instances become
available. Imported and applied views retain helper references and distinct
model-local bindings, while the separate display remains ordinary problem syntax.
-/

namespace MorewTest.Reformulation.ConeMembershipReplay

open Morew Morew.Conic MorewTest.Reformulation.ConeMembership
noncomputable section

def source :=
  problem (x y : ℝ)
    minimize @Zero.zero ℝ inferInstance
    subject to
      equal : x = y
      upper : x ≤ 0
      leftZero : 0 = y
      numeric : (2 : ℝ) = 3

reformulation target : source := by
  conic

-- A same-spelled helper in the importing namespace must not capture references
-- recovered from the checked imported declaration.
def shifted (_offset x : ℝ) : ℝ := x - 100

reformulation applied : (Defined.source 2) := by
  conic

private partial def containsIdentifier (stx : Lean.Syntax) (name : Lean.Name) : Bool :=
  (stx.isIdent && stx.getId.eraseMacroScopes == name) ||
    stx.getArgs.any (containsIdentifier · name)

run_cmd do
  for name in #[``Defined.target, ``applied] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing imported or applied replay metadata"
    unless view.definitions.map (·.name.eraseMacroScopes) == #[`first, `second, `unused] do
      Lean.throwError "exact replay changed model-local binding identity or order"
    unless containsIdentifier view.objective `first do
      Lean.throwError "exact replay expanded the objective's model-local binding"
    for binding in #[`first, `second] do
      unless containsIdentifier view.constraints[1]!.proposition binding do
        Lean.throwError "exact replay merged distinct model-local bindings"

section ChangedInstances

-- These instances did not exist when either target was registered. Arbitrary
-- replacements make each equality below check that replay uses the old checked
-- instances, including operations retained inside local definitions.
variable [changedSub : HSub ℝ ℝ ℝ] [changedNeg : Neg ℝ] [changedZero : Zero ℝ]
  [changedNumeral : ∀ n : Nat, OfNat ℝ n]
  [changedMembership : Membership ℝ (Set ℝ)] [changedSingleton : Singleton ℝ (Set ℝ)]

run_cmd do
  for (source, copied) in #[(``target, `replayed), (``applied, `replayedApplied)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) source
      | Lean.throwError "missing exact replay metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copied
    Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x y : ℝ) : replayed.feasible (x, y) ↔ target.feasible (x, y) := Iff.rfl
example (x y : ℝ) : replayed.objective (x, y) = target.objective (x, y) := rfl
example (x : ℝ) : replayedApplied.feasible x ↔ applied.feasible x := Iff.rfl
example (x : ℝ) : replayedApplied.objective x = applied.objective x := rfl

section ImportedParameter

variable (offset : ℝ)

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``Defined.target
    | Lean.throwError "missing imported exact replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayedImported
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : (replayedImported offset).feasible x ↔
    (Defined.target offset).feasible x := Iff.rfl
example (x : ℝ) : (replayedImported offset).objective x =
    (Defined.target offset).objective x := rfl

end ImportedParameter

reformulation continued : applied := by
  conic

example : GlobalEquivalence applied continued := continued.equivalence
example (x : ℝ) : continued.feasible x ↔ applied.feasible x := Iff.rfl

/--
info: problem (x y : ℝ)
  minimize Zero.zero
  subject to
    equal : x - y ∈ ({0} : Set ℝ)
    upper : -x ∈ ℝ₊
    leftZero : -y ∈ ({0} : Set ℝ)
    numeric : 2 - 3 ∈ ({0} : Set ℝ)
-/
#guard_msgs in
#printp target

end ChangedInstances

-- A view remains an editable syntax value. Replacing fields after lookup must
-- affect reconstruction; no cached replay of the old complete problem may win.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing editable replay metadata"
  let view := { view with objective := Lean.mkIdent `y, constraints := #[] }
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `modified
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x y : ℝ) : modified.objective (x, y) = y := rfl
example (x y : ℝ) : modified.feasible (x, y) ↔ True := Iff.rfl

namespace ImportedNamedParameters

-- A producer's named instance need not retain its local name in the importing
-- context. Reconstruct both fields and the retained definition with the caller's
-- instance, just as applying the imported target does.
section
variable [Defined.NamedParameter]

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``Defined.namedTarget
    | Lean.throwError "missing imported named-instance replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `anonymousReplay
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : anonymousReplay.feasible x ↔ Defined.namedTarget.feasible x := Iff.rfl
example (x : ℝ) : anonymousReplay.objective x = Defined.namedTarget.objective x := rfl

end

-- A global with the old parameter's spelling is not the formal local instance.
abbrev configuration : Defined.NamedParameter := ⟨37⟩

section
variable [replacement : Defined.NamedParameter]

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``Defined.namedTarget
    | Lean.throwError "missing renamed-instance replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `renamedReplay
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : renamedReplay.feasible x ↔ Defined.namedTarget.feasible x := Iff.rfl
example (x : ℝ) : renamedReplay.objective x = Defined.namedTarget.objective x := rfl

section
variable (configuration : Nat)

-- A same-spelled local of another type must not capture the instance either.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``Defined.namedTarget
    | Lean.throwError "missing shadowed-instance replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `shadowedReplay
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : shadowedReplay.feasible x ↔ Defined.namedTarget.feasible x := Iff.rfl
example (x : ℝ) : shadowedReplay.objective x = Defined.namedTarget.objective x := rfl

end
end
end ImportedNamedParameters

namespace NamedInstances

-- Distinct parameters of the same class are intentional in this replay test.
set_option linter.overlappingInstances false

class Parameter where
  value : ℝ

variable [first : Parameter] [second : Parameter]

def source :=
  problem (x : ℝ)
    let left := @Parameter.value first
    let right := @Parameter.value second
    minimize left
    subject to bounds : x ≤ left ∧ right ≤ x

-- Both instance arguments are intentional. Ordinary synthesis would choose
-- the last instance for both and erase the distinction between the bindings.
reformulation target : (@source first second) := by
  conic

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing named-instance replay metadata"
  unless containsIdentifier view.definitions[0]!.value `first &&
      containsIdentifier view.definitions[1]!.value `second do
    Lean.throwError "exact replay merged distinct named instance parameters"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : (@replayed first second).feasible x ↔
    (@target first second).feasible x := Iff.rfl
example (x : ℝ) : (@replayed first second).objective x =
    (@target first second).objective x := rfl

end NamedInstances

namespace InstanceNameCollision

class Coeff where
  c : ℝ

variable [coeff : Coeff]

def source :=
  problem (coeff : ℝ)
    minimize Coeff.c + coeff
    subject to equal : coeff = Coeff.c

reformulation target : source := by
  conic

-- The decision name forces the declaration's instance parameter to be renamed
-- while rendering. That fresh display name is unavailable to the replay caller.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing collision-safe instance replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : replayed.feasible x ↔ target.feasible x := Iff.rfl
example (x : ℝ) : replayed.objective x = target.objective x := rfl

reformulation continued : target := by
  conic

example : GlobalEquivalence target continued := continued.equivalence
example (x : ℝ) : continued.feasible x ↔ target.feasible x := Iff.rfl

/--
info: problem (coeff : ℝ)
  minimize Coeff.c + coeff
  subject to
    equal : coeff - Coeff.c ∈ ({0} : Set ℝ)
-/
#guard_msgs in
#printp target

namespace Distinct

set_option linter.overlappingInstances false
variable [other : Coeff]

-- Capture both instances before introducing the same-spelled decision. The
-- registration helper must retain each explicit identity, even though ordinary
-- inference would choose `other` for both.
def source :=
  let firstValue := @Coeff.c coeff
  let secondValue := @Coeff.c other
  problem (coeff : ℝ)
    let left := firstValue
    let right := secondValue
    minimize left + right + coeff
    subject to equal : coeff = left

run_cmd do
  let some template := Syntax.getProblemView? (← Lean.getEnv) ``source
    | Lean.throwError "missing distinct collision source metadata"
  Morew.Reformulation.Internal.refreshProblemView ``source template
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``source
    | Lean.throwError "missing distinct collision replay metadata"
  unless containsIdentifier view.definitions[0]!.value `coeff &&
      containsIdentifier view.definitions[1]!.value `other do
    Lean.throwError "replay inferred away distinct colliding instance parameters"
  unless view.binders[0]!.name.hasMacroScopes do
    Lean.throwError "replay did not distinguish the colliding decision name"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : (@replayed coeff other).feasible x ↔
    (@source coeff other).feasible x := Iff.rfl
example (x : ℝ) : (@replayed coeff other).objective x =
    @Coeff.c coeff + @Coeff.c other + x := rfl

end Distinct
end InstanceNameCollision

namespace RenamedInstanceCollision

variable [replacement : InstanceNameCollision.Coeff]

-- The replay decision is hygienically scoped because it originally collided
-- with the producer's instance. It must still replay after that section ends.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``InstanceNameCollision.target
    | Lean.throwError "missing renamed collision replay metadata"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x : ℝ) : replayed.feasible x ↔ InstanceNameCollision.target.feasible x := Iff.rfl
example (x : ℝ) : replayed.objective x = InstanceNameCollision.target.objective x := rfl

end RenamedInstanceCollision

end
end MorewTest.Reformulation.ConeMembershipReplay
