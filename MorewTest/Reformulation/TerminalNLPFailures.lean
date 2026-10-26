/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Terminal smooth-NLP rejection and complete rollback

Failures in certification, companion-name preflight, and late property emission
must leave no public declarations, auxiliary declarations, or presentation data.
-/

namespace MorewTest.Reformulation.TerminalNLPFailures

open Morew
noncomputable section

elab "assert_nlp_terminal_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let `(command| reformulation $target:ident : $_source:ident
      $[certificate $_alias:ident]? := by $_steps:reformulationStep*) := nested
    | Lean.throwError "expected a reformulation command"
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  for (name, _) in after.constants.toList do
    unless before.contains name do
      Lean.throwError m!"failed terminal NLP conversion leaked declaration {name}"
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed terminal NLP conversion leaked presentation metadata"

def smoothSource := problem (x : ℝ) minimize x ^ 2 subject to bound : 0 ≤ x

namespace FormCollision
def target.nlpForm : Nat := 17
/-- error: `MorewTest.Reformulation.TerminalNLPFailures.FormCollision.target.nlpForm` has already been declared -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation target : smoothSource certificate aliasProof := by
  nlp
example : target.nlpForm = 17 := rfl
end FormCollision

namespace PropertyCollision
def target.isSmoothNLP : Nat := 19
/-- error: `MorewTest.Reformulation.TerminalNLPFailures.PropertyCollision.target.isSmoothNLP` has already been declared -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation target : smoothSource certificate aliasProof := by
  nlp
example : target.isSmoothNLP = 19 := rfl
end PropertyCollision

/-- error: duplicate generated declaration name -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation aliasIsForm : smoothSource certificate aliasIsForm.nlpForm := by
  nlp

/-- error: duplicate generated declaration name -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation aliasIsProperty : smoothSource certificate aliasIsProperty.isSmoothNLP := by
  nlp

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_nlp_terminal_atomic%
reformulation afterTerminal : smoothSource := by
  nlp
  epigraph t

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_nlp_terminal_atomic%
reformulation conicAfterTerminal : smoothSource := by
  nlp
  conic

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_nlp_terminal_atomic%
reformulation nlpAfterConic : smoothSource := by
  epigraph t
  conic
  nlp

def nonsmoothObjective := problem (x : ℝ) minimize |x|
/-- error: not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noImplicitObjectiveLift : nonsmoothObjective := by
  nlp

def zeroBoundary :=
  problem (x : ℝ)
    minimize Real.sqrt x
    subject to lower : 0 ≤ x
/-- error: not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noBoundaryDomain : zeroBoundary := by
  nlp

def strictRows := problem (x : ℝ) minimize x subject to strict : 0 < x
/-- error: constraint `strict` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noStrictRows : strictRows := by
  nlp

def nonsmoothEquality := problem (x : ℝ) minimize x subject to equality : |x| = 1
/-- error: constraint `equality` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noAutomaticGraph : nonsmoothEquality := by
  nlp

def nestedNonsmooth := problem (x : ℝ) minimize x subject to nested : |x| + x ≤ 1
/-- error: constraint `nested` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noNestedAutomaticLift : nestedNonsmooth := by
  nlp

def badConstant := problem (x : ℝ) minimize x + Real.log (-1)
/-- error: not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noInvalidConstantDomain : badConstant := by
  nlp

def unsupportedSpace := problem (_choice : Bool) minimize (0 : ℝ)
/-- error: not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noBooleanSpace : unsupportedSpace := by
  nlp

opaque alteredLE : LE ℝ := ⟨fun _ _ => True⟩
def alteredOrder := problem (x : ℝ) minimize x subject to fake : @LE.le ℝ alteredLE x 1
/-- error: constraint `fake` is not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation noAlteredOrder : alteredOrder := by
  nlp

-- A successful rewrite creates proof helpers before objective certification
-- fails. Neither targeted nor terminal preparation may leak those helpers.
def lateObjectiveFailure :=
  problem (x t : ℝ)
    minimize Real.log x
    subject to magnitude : |x| ≤ t

/-- error: not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation rollbackAfterTargeted : lateObjectiveFailure := by
  nlp at magnitude
  nlp

/-- error: not certified as a smooth NLP by the available rules: -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation rollbackInsideTerminal : lateObjectiveFailure := by
  nlp

section LateCompanionFailure
@[local term_elab Lean.Parser.Term.app]
private def rejectTerminalProperty : Lean.Elab.Term.TermElab := fun _ _ => do
  if (← Lean.getEnv).contains
      `MorewTest.Reformulation.TerminalNLPFailures.lateFailure.nlpForm then
    Lean.throwError "injected terminal NLP property emission failure"
  Lean.Elab.throwUnsupportedSyntax

/-- error: injected terminal NLP property emission failure -/
#guard_msgs (substring := true) in
assert_nlp_terminal_atomic%
reformulation lateFailure : smoothSource certificate lateFailureAlias := by
  nlp
end LateCompanionFailure

end
end MorewTest.Reformulation.TerminalNLPFailures
