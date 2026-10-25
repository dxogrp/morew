/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Terminal conic failure and declaration atomicity

Every rejected command preserves the complete declaration environment, including
private proof helpers created by earlier successful steps. Public target,
equivalence, form, representability, and alias names are all preflighted.
-/

namespace MorewTest.Reformulation.TerminalConicFailures

open Morew
noncomputable section

elab "assert_terminal_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let `(command| reformulation $target:ident : $_source:ident
      $[certificate $_alias:ident]? := by $_steps:reformulationStep*) := nested
    | Lean.throwError "expected a reformulation command"
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  for (name, _) in after.constants.toList do
    unless before.contains name do
      Lean.throwError m!"failed terminal conversion leaked declaration {name}"
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed terminal conversion leaked presentation metadata"

def affineSource :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : 0 ≤ x

namespace TargetCollision
def target : Nat := 11
/-- error: `MorewTest.Reformulation.TerminalConicFailures.TargetCollision.target` has already been declared -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation target : affineSource certificate certificateAlias := by
  conic
example : target = 11 := rfl
end TargetCollision

namespace EquivalenceCollision
def target.equivalence : Nat := 13
/-- error: `MorewTest.Reformulation.TerminalConicFailures.EquivalenceCollision.target.equivalence` has already been declared -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation target : affineSource certificate certificateAlias := by
  conic
example : target.equivalence = 13 := rfl
end EquivalenceCollision

namespace FormCollision
def target.conicForm : Nat := 17
/-- error: `MorewTest.Reformulation.TerminalConicFailures.FormCollision.target.conicForm` has already been declared -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation target : affineSource certificate certificateAlias := by
  conic
example : target.conicForm = 17 := rfl
end FormCollision

namespace IsConicCollision
def target.isConic : Nat := 19
/-- error: `MorewTest.Reformulation.TerminalConicFailures.IsConicCollision.target.isConic` has already been declared -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation target : affineSource certificate certificateAlias := by
  conic
example : target.isConic = 19 := rfl
end IsConicCollision

namespace AliasCollision
def certificateAlias : Nat := 23
/-- error: `MorewTest.Reformulation.TerminalConicFailures.AliasCollision.certificateAlias` has already been declared -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation target : affineSource certificate certificateAlias := by
  conic
example : certificateAlias = 23 := rfl
end AliasCollision

/-- error: duplicate generated declaration name -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation aliasIsForm : affineSource certificate aliasIsForm.conicForm := by
  conic

/-- error: duplicate generated declaration name -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation aliasIsConic : affineSource certificate aliasIsConic.isConic := by
  conic

/-- error: certificate alias names the same declaration as the reformulation target -/
#guard_msgs in
assert_terminal_atomic%
reformulation aliasIsTarget : affineSource certificate aliasIsTarget := by
  conic

/-- error: certificate alias names the same declaration as the canonical certificate -/
#guard_msgs in
assert_terminal_atomic%
reformulation aliasIsEquivalence : affineSource certificate aliasIsEquivalence.equivalence := by
  conic

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_terminal_atomic%
reformulation afterTerminal : affineSource certificate afterTerminalAlias := by
  conic
  epigraph t

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_terminal_atomic%
reformulation twiceTerminal : affineSource := by
  conic
  conic

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_terminal_atomic%
reformulation targetedAfterTerminal : affineSource := by
  conic
  conic at bound

def nonlinearMinimum := problem (x : ℝ) minimize |x|

/-- error: terminal conic validation is uncertified: objective: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noAutomaticEpigraph : nonlinearMinimum := by
  conic

def nonlinearMaximum :=
  problem (x : ℝ)
    maximize Real.log x
    subject to
      margin : 1 ≤ x

/-- error: terminal conic validation is uncertified: objective: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noAutomaticHypograph : nonlinearMaximum := by
  conic

def missingMargin :=
  problem (x t : ℝ)
    minimize t
    subject to
      logarithm : t ≤ Real.log x

/-- error: terminal conic validation is uncertified: constraint `logarithm`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noMargin : missingMargin := by
  conic

def onlyZeroMargin :=
  problem (x t : ℝ)
    minimize t
    subject to
      margin : 0 ≤ x
      logarithm : t ≤ Real.log x

/-- error: terminal conic validation is uncertified: constraint `logarithm`: logarithm rewrite was not certified: missing positive constant margin -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noStrictMargin : onlyZeroMargin := by
  conic

def derivedMargin :=
  problem (x y t : ℝ)
    minimize t
    subject to
      lower : 1 ≤ y
      comparison : y ≤ x
      logarithm : t ≤ Real.log x

/-- error: terminal conic validation is uncertified: constraint `logarithm`: logarithm rewrite was not certified: missing positive constant margin -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noArithmeticDomainSearch : derivedMargin := by
  conic

def quadraticWithoutMargin :=
  problem (x y t : ℝ)
    minimize t
    subject to
      ratio : x ^ 2 / y ≤ t

/-- error: terminal conic validation is uncertified: constraint `ratio`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noQuadraticDenominatorMargin : quadraticWithoutMargin := by
  conic

def entropyWithoutNumeratorMargin :=
  problem (a b t : ℝ)
    minimize t
    subject to
      denominator : 1 ≤ b
      entropy : Fn.relativeEntropy a b ≤ t

/-- error: terminal conic validation is uncertified: constraint `entropy`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noEntropyNumeratorMargin : entropyWithoutNumeratorMargin := by
  conic

def emptyLogSumExp :=
  problem (v : Fin 0 → ℝ) (t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp v ≤ t

/-- error: terminal conic validation is uncertified: constraint `lse`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noEmptyLogSumExp : emptyLogSumExp := by
  conic

def strictSource :=
  problem (x : ℝ)
    minimize x
    subject to
      strict : 0 < x

/-- error: terminal conic validation is uncertified: constraint `strict`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noStrictRow : strictSource := by
  conic

def nonlinearEquality :=
  problem (x : ℝ)
    minimize x
    subject to
      equality : x ^ 2 = 1

/-- error: terminal conic validation is uncertified: constraint `equality`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noNonlinearEquality : nonlinearEquality := by
  conic

opaque hiddenAffine (x : ℝ) : ℝ := x + 1
def opaqueSource :=
  problem (x : ℝ)
    minimize x
    subject to
      hidden : hiddenAffine x ≤ 3

/-- error: terminal conic validation is uncertified: constraint `hidden`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noHelperUnfolding : opaqueSource := by
  conic

def nonlinearCoordinates :=
  problem (x t : ℝ)
    minimize t
    subject to
      nested : Fn.softplus (x ^ 2) ≤ t

/-- error: terminal conic validation is uncertified: constraint `nested`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noRecursiveAtomLifting : nonlinearCoordinates := by
  conic

def unsupportedSpace := problem (_choice : Bool) minimize (0 : ℝ)

/-- error: terminal conic validation is uncertified: objective: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noBooleanSpace : unsupportedSpace := by
  conic

private opaque incompatibleOrder : LE ℝ := ⟨fun _ _ => True⟩

def customOrder :=
  problem (x : ℝ)
    minimize x
    subject to
      fake : @LE.le ℝ incompatibleOrder x 1

/-- error: terminal conic validation is uncertified: constraint `fake`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noCustomOrder : customOrder := by
  conic

def groupedCustomOrder :=
  problem (x : ℝ)
    minimize x
    subject to
      fake : @LE.le ℝ incompatibleOrder x 1 ∧ x = 0

/-- error: terminal conic validation is uncertified: constraint `fake`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noGroupedCustomOrder : groupedCustomOrder := by
  conic

private opaque incompatibleMembership :
    Membership (ℝ × ℝ × ℝ) (ConvexCone ℝ (ℝ × ℝ × ℝ)) := ⟨fun _ _ => True⟩

def customMembership :=
  problem (x : ℝ)
    minimize x
    subject to
      fake : @Membership.mem (ℝ × ℝ × ℝ) (ConvexCone ℝ (ℝ × ℝ × ℝ))
        incompatibleMembership Conic.Cone.exponential.carrier (x, 1, x)

/-- error: terminal conic validation is uncertified: constraint `fake`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation noCustomMembership : customMembership := by
  conic

-- The surface checkpoint already reduces an explicit constant relation to
-- True. Terminal conversion certifies that exact normalized predicate without
-- applying a native rule to the discarded operation instance.
def reducibleConstantRelations :=
  problem (x : ℝ)
    minimize x
    subject to
      order : @LE.le ℝ ⟨fun _ _ => True⟩ x 1
      membership : @Membership.mem (ℝ × ℝ × ℝ) (ConvexCone ℝ (ℝ × ℝ × ℝ))
        ⟨fun _ _ => True⟩ Conic.Cone.exponential.carrier (x, 1, x)

reformulation constantRelationsTarget : reducibleConstantRelations := by
  conic

example : constantRelationsTarget.conicForm.data.rowCount = 0 := rfl
example : GlobalEquivalence reducibleConstantRelations constantRelationsTarget :=
  constantRelationsTarget.equivalence

-- Normalizing an affine sibling must not reinterpret a constant relation that
-- the semantic checkpoint already reduced to True. Keep its original leaf,
-- the nested conjunctions, and the separate model-local binding identities.
structure PropositionHolder where
  proposition : Prop

def groupedConstantRelations :=
  problem (x y : ℝ)
    let first := x
    let second := y
    minimize first
    subject to
      grouped : (@LE.le ℝ ⟨fun _ _ => True⟩ first 1 ∧ first = second) ∧
        (let order : LE ℝ := ⟨fun _ _ => True⟩;
          @LE.le ℝ order second 0 ∧ @LE.le ℝ Real.instLE second 5)
      emptyConjunction : @LE.le ℝ ⟨fun _ _ => True ∧ True⟩ first 1 ∧ second = 0
      affineConjunction : @LE.le ℝ ⟨fun a b => (a ≤ b) ∧ True⟩ first second ∧ True
      customMembership : @Membership.mem ℝ (Set ℝ) ⟨fun _ value => value ≤ 0⟩
        ({0} : Set ℝ) first ∧ second = 0
      membershipConjunction : @Membership.mem ℝ (Set ℝ)
        ⟨fun _ value => value ≤ 0 ∧ True⟩ ({0} : Set ℝ) first ∧ True
      reverseRelation : @LE.le ℝ ⟨fun a b => b ≤ a⟩ first second ∧ True
      nativeMembership : (first, 1, second) ∈ Conic.Cone.exponential.carrier ∧ first ≤ second
      constantMatch : (match true with | true => first ≤ 0 | false => first = 1) ∧ second = 0
      fieldProjection : (PropositionHolder.mk (first ≤ 0)).proposition ∧ second = 0

reformulation groupedConstantTarget : groupedConstantRelations := by
  conic

example : GlobalEquivalence groupedConstantRelations groupedConstantTarget :=
  groupedConstantTarget.equivalence
example : groupedConstantTarget.conicForm.data.rowCount = 14 := rfl
example : groupedConstantTarget.conicForm.data.toProblem = groupedConstantTarget :=
  groupedConstantTarget.conicForm.represents
example (x y : ℝ) : groupedConstantTarget.feasible (x, y) ↔
    ((True ∧ x - y ∈ ({0} : Set ℝ)) ∧ (True ∧ 5 - y ∈ ℝ₊)) ∧
      ((True ∧ True) ∧ y ∈ ({0} : Set ℝ)) ∧ ((y - x ∈ ℝ₊ ∧ True) ∧ True) ∧
        (-x ∈ ℝ₊ ∧ y ∈ ({0} : Set ℝ)) ∧ ((-x ∈ ℝ₊ ∧ True) ∧ True) ∧
          (x - y ∈ ℝ₊ ∧ True) ∧ ((x, 1, y) ∈ Conic.Cone.exponential.carrier ∧ y - x ∈ ℝ₊) ∧
            (-x ∈ ℝ₊ ∧ y ∈ ({0} : Set ℝ)) ∧
            (-x ∈ ℝ₊ ∧ y ∈ ({0} : Set ℝ)) := Iff.rfl

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``groupedConstantTarget
    | Lean.throwError "missing grouped constant-relation presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`grouped, `emptyConjunction, `affineConjunction, `customMembership,
        `membershipConjunction, `reverseRelation, `nativeMembership, `constantMatch,
        `fieldProjection] &&
      view.definitions.map (·.name.eraseMacroScopes) == #[`first, `second] do
    Lean.throwError "constant-relation normalization changed presentation bindings"
  Lean.Elab.Command.liftTermElabM do
    let some value := (← Lean.getConstInfo ``groupedConstantTarget).value?
      | Lean.throwError "missing grouped constant-relation target"
    unless (value.find? (·.isAppOfArity ``LE.le 4)).isSome do
      Lean.throwError "constant-relation normalization erased the retained comparison leaf"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `groupedConstantReplayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x y : ℝ) : groupedConstantReplayed.feasible (x, y) ↔
    groupedConstantTarget.feasible (x, y) := Iff.rfl

reformulation groupedConstantAgain : groupedConstantTarget := by
  epigraph t
  conic

example : groupedConstantAgain.conicForm.data.rowCount = 15 := rfl
example : GlobalEquivalence groupedConstantTarget groupedConstantAgain :=
  groupedConstantAgain.equivalence

def liftedThenFailure :=
  problem (x t : ℝ)
    minimize t
    subject to
      loss : Fn.softplus x ≤ t
      logarithm : t ≤ Real.log x

/-- error: terminal conic validation is uncertified: constraint `logarithm`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation rollbackAfterTargetedSuccess : liftedThenFailure
    certificate rollbackAfterTargetedAlias := by
  conic at loss
  conic

/-- error: terminal conic validation is uncertified: constraint `logarithm`: -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation rollbackInsideTerminal : liftedThenFailure
    certificate rollbackInsideTerminalAlias := by
  conic

def absoluteSource :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : |x| ≤ 1

/-- error: unknown or stale constraint label `bound` -/
#guard_msgs in
assert_terminal_atomic%
reformulation staleBeforeTerminal : absoluteSource := by
  conic at bound
  conic at bound
  conic

/-- error: unknown or stale constraint label `absent` -/
#guard_msgs in
assert_terminal_atomic%
reformulation unknownBeforeTerminal : absoluteSource := by
  conic at absent
  conic

section LateCompanionFailure

-- Inject an elaboration failure only after the named form has been published
-- inside the transaction. This tests rollback beyond planning and preflight.
@[local term_elab Lean.Parser.Term.app]
private def rejectTerminalProperty : Lean.Elab.Term.TermElab := fun _ _ => do
  if (← Lean.getEnv).contains
      `MorewTest.Reformulation.TerminalConicFailures.lateFailure.conicForm then
    Lean.throwError "injected terminal property emission failure"
  Lean.Elab.throwUnsupportedSyntax

/-- error: injected terminal property emission failure -/
#guard_msgs (substring := true) in
assert_terminal_atomic%
reformulation lateFailure : absoluteSource certificate lateFailureAlias := by
  conic

end LateCompanionFailure

end
end MorewTest.Reformulation.TerminalConicFailures
