/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew
import MorewTest.Diagnostics
import MorewTest.Environment
import MorewTest.Reformulation.PowerSource

/-!
# Power-cone command integration

These examples check ordered targets, auxiliary coordinates, terminal forms,
readable power-set notation, exact presentation replay, and imported models.
-/

namespace MorewTest.Reformulation.Power

open Morew Morew.Conic

noncomputable section

namespace Scalar

def source :=
  problem (x t : ℝ)
    let base := 2 * x + 1
    minimize t
    subject to
      before : 0 ≤ base
      bound : Real.rpow base (3 / 2) ≤ t
      after : t ≤ 10

reformulation targeted : source := by
  conic at bound

reformulation terminal : source := by
  conic

example : GlobalEquivalence source targeted := targeted.equivalence
example : GlobalEquivalence source terminal := terminal.equivalence
example : Conic.Form terminal := terminal.conicForm
example : terminal.conicForm.data.toProblem = terminal := terminal.conicForm.represents
example : terminal.conicForm.data.rowCount = 3 := rfl
example (x t : ℝ) : targeted.feasible (x, t) ↔
    0 ≤ 2 * x + 1 ∧ (t, 1, 2 * x + 1) ∈ POW (2 / 3) ∧ t ≤ 10 := Iff.rfl
example (x t : ℝ) : targeted.objective (x, t) = t := rfl

def negativeSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      positive : 1 / 2 ≤ x
      bound : x ^ (-2 : ℝ) ≤ t

reformulation negativeTarget : negativeSource := by
  conic

example : GlobalEquivalence negativeSource negativeTarget := negativeTarget.equivalence
example : Conic.Form negativeTarget := negativeTarget.conicForm
example (x t : ℝ) : negativeTarget.feasible (x, t) ↔
    x - 1 / 2 ∈ ℝ₊ ∧ (t, x, 1) ∈ POW (1 / 3) := Iff.rfl

def negativeFractionSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      positive : 1 ≤ x
      bound : x ^ (-1 / 2 : ℝ) ≤ t

reformulation negativeFractionTarget : negativeFractionSource := by
  conic at bound

reformulation negativeFractionTerminal : negativeFractionSource := by
  conic

example : GlobalEquivalence negativeFractionSource negativeFractionTarget :=
  negativeFractionTarget.equivalence
example (x t : ℝ) : negativeFractionTarget.feasible (x, t) ↔
    1 ≤ x ∧ (t, x, 1) ∈ POW (2 / 3) := Iff.rfl
example (x t : ℝ) : negativeFractionTerminal.feasible (x, t) ↔
    x - 1 ∈ ℝ₊ ∧ (t, x, 1) ∈ POW (2 / 3) := Iff.rfl
example : negativeFractionTerminal.conicForm.data.toProblem = negativeFractionTerminal :=
  negativeFractionTerminal.conicForm.represents

def constantSource :=
  problem (t : ℝ)
    minimize t
    subject to
      positive : Real.rpow 2 (3 / 2) ≤ t
      negative : Real.rpow 2 (-2) ≤ t

reformulation constantTarget : constantSource := by
  conic at positive
  conic at negative
  conic

example : GlobalEquivalence constantSource constantTarget := constantTarget.equivalence
example : Conic.Form constantTarget := constantTarget.conicForm

end Scalar

namespace Hypograph

def source :=
  problem (x t : ℝ)
    maximize t
    subject to
      nonnegative : 0 ≤ x
      bound : t ≤ x ^ (1 / 2 : ℝ)

reformulation target : source := by
  conic at bound

reformulation terminal : target := by
  conic

example : GlobalEquivalence source target := target.equivalence
example : Problem ((ℝ × ℝ) × ℝ) (OrderDual ℝ) := target
example : terminal.conicForm.data.sense = .maximize := rfl
example : terminal.conicForm.data.rowCount = 4 := rfl
example (x t u : ℝ) : target.feasible ((x, t), u) ↔
    0 ≤ x ∧ 0 ≤ u ∧ t ≤ u ∧ (x, 1, u) ∈ POW (1 / 2) := Iff.rfl
-- The added nonnegative coordinate can witness a negative original bound.
example : target.feasible ((0, -1), 0) := by
  change 0 ≤ (0 : ℝ) ∧ 0 ≤ (0 : ℝ) ∧ (-1 : ℝ) ≤ 0 ∧ (0, 1, 0) ∈ POW (1 / 2)
  norm_num [Cone.mem_powerSet]

def meanSource :=
  problem (x y t : ℝ)
    maximize t
    subject to
      nonnegativeX : 0 ≤ x
      bound : t ≤ Real.rpow x (1 / 3) * y ^ (1 - (1 / 3 : ℝ))
      nonnegativeY : 0 ≤ y

reformulation meanTarget : meanSource := by
  conic

example : GlobalEquivalence meanSource meanTarget := meanTarget.equivalence
example : meanTarget.conicForm.data.toProblem = meanTarget := meanTarget.conicForm.represents
example (x y t u : ℝ) : meanTarget.feasible (((x, y), t), u) ↔
    x ∈ ℝ₊ ∧ u ∈ ℝ₊ ∧ u - t ∈ ℝ₊ ∧ (x, y, u) ∈ POW (1 / 3) ∧ y ∈ ℝ₊ := Iff.rfl

end Hypograph

namespace Direct

def source :=
  problem (x y z : ℝ)
    minimize z
    subject to cone : (2 * x + 1, y, z - 1) ∈ POW (1 / 3)

reformulation target : source := by
  conic

example : GlobalEquivalence source target := target.equivalence
example : Conic.Form target := target.conicForm
example : target.conicForm.data.rowCount = 1 := rfl
example (x y z : ℝ) : target.feasible ((x, y), z) ↔
    (2 * x + 1, y, z - 1) ∈ POW (1 / 3) := Iff.rfl

def symbolicSource (α : ℝ) :=
  problem (x y z : ℝ)
    maximize z
    subject to cone : (x, y, z) ∈ POW α

variable (α : ℝ) (hα : 0 < α ∧ α < 1)

include hα in
reformulation symbolicTarget : (symbolicSource α) := by
  conic

example : GlobalEquivalence (symbolicSource α) (symbolicTarget α) :=
  symbolicTarget.equivalence α
example : Conic.Form (symbolicTarget α) := symbolicTarget.conicForm α hα
example : (symbolicTarget.conicForm α hα).data.sense = .maximize := rfl

end Direct

namespace LocalExponent

def source :=
  problem (x t : ℝ)
    let exponent : ℝ := -1 / 2
    minimize t
    subject to
      positive : 1 ≤ x
      bound : x ^ exponent ≤ t
      untouched : exponent ≤ 0

reformulation target : source := by
  conic at bound

example : GlobalEquivalence source target := target.equivalence
example (x t : ℝ) : target.feasible (x, t) ↔
    let exponent : ℝ := -1 / 2
    1 ≤ x ∧ (t, x, 1) ∈ POW (2 / 3) ∧ exponent ≤ 0 := Iff.rfl

end LocalExponent

namespace Imported

-- These conflicting names must not capture the imported source's frozen names.
def exponent : ℝ := -2
def power (_ : ℝ) : ℝ := 0

variable (offset : ℝ)

reformulation target : (PowerSource.source offset) := by
  conic at bound using (Conic.Power.rpowEpigraph PowerSource.exponent PowerSource.exponent_range)

reformulation terminal : (target offset) := by
  conic

example : GlobalEquivalence (PowerSource.source offset) (target offset) := target.equivalence offset
example : Conic.Form (terminal offset) := terminal.conicForm offset
example (x t : ℝ) : (target offset).feasible (x, t) ↔
    0 ≤ x + offset ∧ (t, 1, x + offset) ∈ POW (1 / PowerSource.exponent) ∧ t ≤ 10 := Iff.rfl

run_cmd do
  for (replay, copy) in [(true, `exactCopy), (false, `displayCopy)] do
    let environment ← Lean.getEnv
    let view? := if replay then Morew.Syntax.getProblemView? environment ``target
      else Morew.Syntax.getProblemDisplayView? environment ``target
    let some view := view? | Lean.throwError "missing imported power presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copy
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : exactCopy offset = target offset := rfl
example : displayCopy offset = target offset := rfl

-- The proof-sharing replay scaffold must remain native after a module import.
reformulation importedContinuation : (PowerSource.rewritten offset) := by
  conic

example : Conic.Form (importedContinuation offset) := importedContinuation.conicForm offset

reformulation numericContinuation : PowerSource.numericTarget := by
  conic

example : GlobalEquivalence PowerSource.numericTarget numericContinuation :=
  numericContinuation.equivalence
example : numericContinuation.conicForm.data.toProblem = numericContinuation :=
  numericContinuation.conicForm.represents

end Imported

namespace Symbolic

variable (p : ℝ) (hp : 1 < p)

def source :=
  problem (x t : ℝ)
    minimize t
    subject to
      nonnegative : 0 ≤ x
      bound : Real.rpow x p ≤ t

include hp in
reformulation target : (source p) := by
  conic at bound using (Conic.Power.rpowEpigraph p hp)

example : GlobalEquivalence (source p) (target p hp) := target.equivalence p hp

run_cmd do
  for (replay, copy) in [(true, `exactCopy), (false, `displayCopy)] do
    let environment ← Lean.getEnv
    let view? := if replay then Morew.Syntax.getProblemView? environment ``target
      else Morew.Syntax.getProblemDisplayView? environment ``target
    let some view := view? | Lean.throwError "missing symbolic power presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copy
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : exactCopy p hp = target p hp := rfl
example : displayCopy p = target p hp := rfl

reformulation continued : (target p hp) := by
  conic

example : Conic.Form (continued p hp) := continued.conicForm p hp

end Symbolic

namespace ShadowedMembership

def marker : Set (ℝ × ℝ × ℝ) := Set.univ

-- Using the instance in an untouched row retains it in the target's actual
-- parameter telescope, where it must not capture generated power membership.
variable [Membership (ℝ × ℝ × ℝ) (Set (ℝ × ℝ × ℝ))]

def source :=
  problem (x t : ℝ)
    minimize t
    subject to
      domain : 0 ≤ x
      other : (x, t, x) ∈ marker
      bound : Real.rpow x (3 / 2) ≤ t
      later : Real.rpow x (5 / 2) ≤ t

reformulation target : source := by
  conic at bound

example : GlobalEquivalence source target := target.equivalence

run_cmd do
  for (replay, copy) in [(true, `exactCopy), (false, `displayCopy)] do
    let environment ← Lean.getEnv
    let view? := if replay then Morew.Syntax.getProblemView? environment ``target
      else Morew.Syntax.getProblemDisplayView? environment ``target
    let some view := view? | Lean.throwError "missing shadowed-membership presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copy
    Lean.Elab.Command.elabCommand (← `(def $name := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copy)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "power membership replay contains unresolved terms or placeholders"

example : exactCopy = target := rfl
example : displayCopy = target := rfl

reformulation continued : target := by
  conic at later

example : GlobalEquivalence target continued := continued.equivalence

end ShadowedMembership

-- Re-elaborating stored views checks exact membership instances and cone proofs.
run_cmd do
  for (original, copy) in [(``Scalar.targeted, `scalarCopy),
      (``Scalar.negativeFractionTarget, `negativeFractionCopy),
      (``Hypograph.target, `hypographCopy), (``Direct.target, `directCopy)] do
    let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "missing power presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copy
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : scalarCopy = Scalar.targeted := rfl
example : negativeFractionCopy = Scalar.negativeFractionTarget := rfl
example : hypographCopy = Hypograph.target := rfl
example : directCopy = Direct.target := rfl

-- The readable Set notation also re-elaborates, independently of exact replay.
run_cmd do
  for (original, copy) in [(``Scalar.targeted, `scalarDisplayCopy),
      (``Scalar.negativeFractionTarget, `negativeFractionDisplayCopy),
      (``Hypograph.target, `hypographDisplayCopy), (``Direct.target, `directDisplayCopy)] do
    let some view := Morew.Syntax.getProblemDisplayView? (← Lean.getEnv) original
      | Lean.throwError "missing readable power presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copy
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : scalarDisplayCopy = Scalar.targeted := rfl
example : negativeFractionDisplayCopy = Scalar.negativeFractionTarget := rfl
example : hypographDisplayCopy = Hypograph.target := rfl
example : directDisplayCopy = Direct.target := rfl

reformulation continued : Hypograph.target := by
  hypograph value as objectiveBound
  conic

example : GlobalEquivalence Hypograph.target continued := continued.equivalence
example : Conic.Form continued := continued.conicForm

elab "assert_power_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let `(command| reformulation $target:ident : $_source:ident
      $[certificate $_alias:ident]? := by $_steps:reformulationStep*) := nested
    | Lean.throwError "expected a reformulation command"
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed power rewrite changed local declarations"
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed power rewrite leaked presentation metadata"

def lateSource :=
  problem (x t : ℝ)
    maximize t
    subject to
      nonnegative : 0 ≤ x
      bound : t ≤ x ^ (1 / 2 : ℝ)
      bad : Real.sin x ≤ t

#guard_error_fragments ["constraint `bad`"] in
assert_power_atomic%
reformulation lateFailure : lateSource certificate lateAlias := by
  conic at bound
  conic

/--
info: problem (x t : ℝ)
  let base := 2 * x + 1
  minimize t
  subject to
    before : 0 ≤ base
    bound_conic_1 : (t, 1, 2 * x + 1) ∈ POW (2 / 3)
    after : t ≤ 10
-/
#guard_msgs in
#printp Scalar.targeted

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    positive : x - 1 ∈ ℝ₊
    bound_conic_1 : (t, x, 1) ∈ POW (2 / 3)
-/
#guard_msgs in
#printp Scalar.negativeFractionTerminal

/--
info: problem (x t bound_aux : ℝ)
  maximize t
  subject to
    nonnegative : 0 ≤ x
    bound_conic_1 : 0 ≤ bound_aux
    bound_conic_2 : t ≤ bound_aux
    bound_conic_3 : (x, 1, bound_aux) ∈ POW (1 / 2)
-/
#guard_msgs in
#printp Hypograph.target

/--
info: problem (x y z : ℝ)
  minimize z
  subject to
    cone : (2 * x + 1, y, z - 1) ∈ POW (1 / 3)
-/
#guard_msgs in
#printp Direct.target

/--
info: problem (x t : ℝ)
  let exponent : ℝ := -1 / 2
  minimize t
  subject to
    positive : 1 ≤ x
    bound_conic_1 : (t, x, 1) ∈ POW (2 / 3)
    untouched : exponent ≤ 0
-/
#guard_msgs in
#printp LocalExponent.target

/--
info: problem (x t : ℝ)
  let base := x + offset
  let power := base.rpow PowerSource.exponent
  minimize t
  subject to
    before : 0 ≤ base
    bound_conic_1 : (t, 1, x + offset) ∈ POW (1 / PowerSource.exponent)
    after : t ≤ 10
-/
#guard_msgs in
#printp Imported.target

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    nonnegative : 0 ≤ x
    bound_conic_1 : (t, 1, x) ∈ POW (1 / p)
-/
#guard_msgs in
#printp Symbolic.target

end

end MorewTest.Reformulation.Power
