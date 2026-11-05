/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.DiagnosticsSupport
import MorewTest.Environment

/-! Command adapters reject malformed evidence before committing any declarations. -/

namespace MorewTest.Reformulation.TerminalEvidence

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open Morew Morew.Elab.Reformulation

noncomputable section

def source := problem (x : ℝ) minimize x
def alien := problem (x : ℝ) minimize x + 1
def maximum := problem (x : ℝ) maximize x

reformulation goodConic : source := by conic
reformulation goodNLP : source := by nlp
reformulation alienConic : alien := by conic
reformulation alienNLP : alien := by nlp

-- Test-only syntax alters a proposed reformulation while retaining its checked primitive
-- certificate, names, and presentation.
syntax (name := faultyConic) "test_conic_form " term : reformulationStep
syntax (name := faultyNLP) "test_nlp_form " term : reformulationStep
syntax (name := nonterminalConic) "test_conic_nonterminal" : reformulationStep
syntax (name := nonterminalNLP) "test_nlp_nonterminal" : reformulationStep
syntax (name := faultyRetarget) "test_conic_retarget" : reformulationStep
syntax (name := faultyProperty) "test_nlp_property" : reformulationStep

private def withForm (draft : SurfaceStepDraft) (form : TSyntax `term) : SurfaceStepDraft :=
  { draft with materialize := fun allocation => do
      let result ← draft.materialize allocation
      let some (adapter, _) := result.terminalForm?
        | throwError "expected a terminal form in the backend draft"
      return { result with terminalForm? := some (adapter, form) } }

@[morew_reformulation_step faultyConic]
private def conicForm : StepHandler := fun state step => do
  let `(reformulationStep| test_conic_form $form:term) := step | throwUnsupportedSyntax
  return withForm (← prepareTerminalConic state step) form

@[morew_reformulation_step faultyNLP]
private def nlpForm : StepHandler := fun state step => do
  let `(reformulationStep| test_nlp_form $form:term) := step | throwUnsupportedSyntax
  return withForm (← prepareTerminalNLP state step) form

@[morew_reformulation_step nonterminalConic]
private def continuingForm : StepHandler := fun state step => do
  let draft ← prepareTerminalConic state step
  return { draft with materialize := fun allocation => do
    return { (← draft.materialize allocation) with status := .continue } }

@[morew_reformulation_step nonterminalNLP]
private def continuingNLPForm : StepHandler := fun state step => do
  let draft ← prepareTerminalNLP state step
  return { draft with materialize := fun allocation => do
    return { (← draft.materialize allocation) with status := .continue } }

@[morew_reformulation_step faultyRetarget]
private def retargetedForm : StepHandler := fun state step => do
  let draft ← prepareTerminalConic state step
  return { draft with materialize := fun allocation => do
    let result ← draft.materialize allocation
    let some (adapter, form) := result.terminalForm?
      | throwError "expected a terminal form in the conic draft"
    let adapter := { adapter with
      retarget := fun _ _ _ => pure (mkConst ``alienConic.conicForm) }
    return { result with terminalForm? := some (adapter, form) } }

@[morew_reformulation_step faultyProperty]
private def failedProperty : StepHandler := fun state step => do
  let draft ← prepareTerminalNLP state step
  return { draft with materialize := fun allocation => do
    let result ← draft.materialize allocation
    let some (adapter, form) := result.terminalForm?
      | throwError "expected a terminal form in the NLP draft"
    let adapter := { adapter with property := fun _ => do
      unless (← getEnv).contains
          `MorewTest.Reformulation.TerminalEvidence.lateProperty.nlpForm do
        throwError "property callback ran before form declaration"
      throwError "injected terminal adapter property failure" }
    return { result with terminalForm? := some (adapter, form) } }

elab "assert_evidence_atomic% " target:ident " in " nested:command : command => do
  let before ← getEnv
  let targetName := (← getCurrNamespace) ++ target.getId
  try elabCommand nested catch error => Lean.Elab.logException error
  let after ← getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    throwError "malformed terminal evidence leaked declarations"
  for suffix in #[Name.anonymous, `equiv, `conicForm, `isConic, `nlpForm, `isSmoothNLP] do
    let name := targetName ++ suffix
    if after.contains name then throwError "malformed terminal evidence emitted {name}"
    if (Syntax.getProblemView? after name).isSome ||
        (Syntax.getProblemDisplayView? after name).isSome ||
        (Syntax.getProblemPrintPresentation? after name).isSome then
      throwError "malformed terminal evidence registered presentation metadata"

#guard_error_fragments ["terminal evidence is not a Conic.Form"] in
assert_evidence_atomic% wrongConicType in
reformulation wrongConicType : source := by test_conic_form True.intro

#guard_error_fragments ["terminal evidence is not a NLP.Form"] in
assert_evidence_atomic% wrongNLPType in
reformulation wrongNLPType : source := by test_nlp_form True.intro

#guard_error_fragments ["terminal conic form does not represent the final canonical problem"] in
assert_evidence_atomic% wrongConicProblem in
reformulation wrongConicProblem : source := by test_conic_form alienConic.conicForm

#guard_error_fragments ["terminal smooth NLP form does not represent the final canonical problem"] in
assert_evidence_atomic% wrongNLPProblem in
reformulation wrongNLPProblem : source := by test_nlp_form alienNLP.nlpForm

#guard_error_fragments ["terminal conic form has the wrong objective sense"] in
assert_evidence_atomic% wrongConicSense in
reformulation wrongConicSense : maximum := by test_conic_form goodConic.conicForm

#guard_error_fragments ["terminal smooth NLP form has the wrong objective sense"] in
assert_evidence_atomic% wrongNLPSense in
reformulation wrongNLPSense : maximum := by test_nlp_form goodNLP.nlpForm

#guard_error_fragments ["a conic form requires a terminal result"] in
assert_evidence_atomic% continuing in
reformulation continuing : source := by test_conic_nonterminal

#guard_error_fragments ["a smooth NLP form requires a terminal result"] in
assert_evidence_atomic% continuingNLP in
reformulation continuingNLP : source := by test_nlp_nonterminal

#guard_error_fragments ["terminal conic form does not represent the final canonical problem"] in
assert_evidence_atomic% retargeted in
reformulation retargeted : source := by test_conic_retarget

#guard_error_fragments ["injected terminal adapter property failure"] in
assert_evidence_atomic% lateProperty in
reformulation lateProperty : source := by test_nlp_property

-- Every rejection preserves the ability to reuse the output and companion names.
reformulation lateProperty : source := by nlp
example : IsSmoothNLP lateProperty := lateProperty.isSmoothNLP

end
end MorewTest.Reformulation.TerminalEvidence
