/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public meta import Lean.Elab.Command
public import Morew.Reformulation.Conic
public import Morew.Reformulation.NLP
public import MorewTest.DiagnosticsSupport
public import MorewTest.Environment

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
reformulation goodQuadConic : source := by qconic
reformulation alienQuadConic : alien := by qconic

-- Test-only syntax alters a proposed reformulation while retaining its checked primitive
-- certificate, names, and presentation.
local syntax (name := faultyConic) "test_conic_form " term : reformulationStep
local syntax (name := faultyNLP) "test_nlp_form " term : reformulationStep
local syntax (name := nonterminalConic) "test_conic_nonterminal" : reformulationStep
local syntax (name := nonterminalNLP) "test_nlp_nonterminal" : reformulationStep
local syntax (name := faultyRetarget) "test_conic_retarget" : reformulationStep
local syntax (name := faultyProperty) "test_nlp_property" : reformulationStep
local syntax (name := faultyQuadConic) "test_quadConic_form " term : reformulationStep
local syntax (name := nonterminalQuadConic) "test_quadConic_nonterminal" : reformulationStep
local syntax (name := faultyQuadConicRetarget) "test_quadConic_retarget" : reformulationStep
local syntax (name := faultyQuadConicRetargetSense) "test_quadConic_retarget_sense" : reformulationStep

private meta def withForm (draft : SurfaceStepDraft) (form : TSyntax `term) : SurfaceStepDraft :=
  { draft with materialize := fun allocation => do
      let result ← draft.materialize allocation
      let some (adapter, _) := result.terminalForm?
        | throwError "expected a terminal form in the backend draft"
      return { result with terminalForm? := some (adapter, form) } }

@[local morew_reformulation_step faultyConic]
private meta def conicForm : StepHandler := fun state step => do
  let `(reformulationStep| test_conic_form $form:term) := step | throwUnsupportedSyntax
  return withForm (← prepareTerminalConic state step) form

@[local morew_reformulation_step faultyNLP]
private meta def nlpForm : StepHandler := fun state step => do
  let `(reformulationStep| test_nlp_form $form:term) := step | throwUnsupportedSyntax
  return withForm (← prepareTerminalNLP state step) form

@[local morew_reformulation_step faultyQuadConic]
private meta def quadConicForm : StepHandler := fun state step => do
  let `(reformulationStep| test_quadConic_form $form:term) := step | throwUnsupportedSyntax
  return withForm (← prepareTerminalQuadConic state step) form

@[local morew_reformulation_step nonterminalQuadConic]
private meta def continuingQuadConicForm : StepHandler := fun state step => do
  let draft ← prepareTerminalQuadConic state step
  return { draft with materialize := fun allocation => do
    return { (← draft.materialize allocation) with status := .continue } }

@[local morew_reformulation_step faultyQuadConicRetarget]
private meta def retargetedQuadConicForm : StepHandler := fun state step => do
  let draft ← prepareTerminalQuadConic state step
  return { draft with materialize := fun allocation => do
    let result ← draft.materialize allocation
    let some (adapter, form) := result.terminalForm?
      | throwError "expected a quadratic terminal form"
    let adapter := { adapter with
      retarget := fun _ _ _ => pure (mkConst ``alienQuadConic.quadConicForm) }
    return { result with terminalForm? := some (adapter, form) } }

@[local morew_reformulation_step faultyQuadConicRetargetSense]
private meta def retargetedQuadConicSense : StepHandler := fun state step => do
  let draft ← prepareTerminalQuadConic state step
  return { draft with materialize := fun allocation => do
    let result ← draft.materialize allocation
    let some (adapter, form) := result.terminalForm?
      | throwError "expected a quadratic terminal form"
    let adapter := { adapter with
      retarget := fun _ _ _ => pure (mkConst ``goodQuadConic.quadConicForm) }
    return { result with terminalForm? := some (adapter, form) } }

@[local morew_reformulation_step nonterminalConic]
private meta def continuingForm : StepHandler := fun state step => do
  let draft ← prepareTerminalConic state step
  return { draft with materialize := fun allocation => do
    return { (← draft.materialize allocation) with status := .continue } }

@[local morew_reformulation_step nonterminalNLP]
private meta def continuingNLPForm : StepHandler := fun state step => do
  let draft ← prepareTerminalNLP state step
  return { draft with materialize := fun allocation => do
    return { (← draft.materialize allocation) with status := .continue } }

@[local morew_reformulation_step faultyRetarget]
private meta def retargetedForm : StepHandler := fun state step => do
  let draft ← prepareTerminalConic state step
  return { draft with materialize := fun allocation => do
    let result ← draft.materialize allocation
    let some (adapter, form) := result.terminalForm?
      | throwError "expected a terminal form in the conic draft"
    let adapter := { adapter with
      retarget := fun _ _ _ => pure (mkConst ``alienConic.conicForm) }
    return { result with terminalForm? := some (adapter, form) } }

@[local morew_reformulation_step faultyProperty]
private meta def failedProperty : StepHandler := fun state step => do
  let draft ← prepareTerminalNLP state step
  return { draft with materialize := fun allocation => do
    let result ← draft.materialize allocation
    let some (adapter, form) := result.terminalForm?
      | throwError "expected a terminal form in the NLP draft"
    let adapter := { adapter with property := fun _ => do
      let env ← getEnv
      let name := `MorewTest.Reformulation.TerminalEvidence.lateProperty.nlpForm
      unless #[name, Lean.mkPrivateName env name].any env.contains do
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
  for suffix in #[Name.anonymous, `equiv, `conicForm, `isConic, `quadConicForm, `isQuadConic,
      `nlpForm, `isSmoothNLP] do
    let name := targetName ++ suffix
    for name in #[name, Lean.mkPrivateName after name] do
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

#guard_error_fragments ["terminal evidence is not a QuadConic.Form"] in
assert_evidence_atomic% wrongQuadConicType in
reformulation wrongQuadConicType : source := by test_quadConic_form True.intro

#guard_error_fragments ["terminal quadratic conic form does not represent the final canonical problem"] in
assert_evidence_atomic% wrongQuadConicProblem in
reformulation wrongQuadConicProblem : source := by
  test_quadConic_form alienQuadConic.quadConicForm

#guard_error_fragments ["terminal quadratic conic form has the wrong objective sense"] in
assert_evidence_atomic% wrongQuadConicSense in
reformulation wrongQuadConicSense : maximum := by
  test_quadConic_form goodQuadConic.quadConicForm

#guard_error_fragments ["a quadratic conic form requires a terminal result"] in
assert_evidence_atomic% continuingQuadConic in
reformulation continuingQuadConic : source := by test_quadConic_nonterminal

#guard_error_fragments ["terminal quadratic conic form does not represent the final canonical problem"] in
assert_evidence_atomic% retargetedQuadConic in
reformulation retargetedQuadConic : source := by test_quadConic_retarget

#guard_error_fragments ["terminal quadratic conic form has the wrong objective sense"] in
assert_evidence_atomic% retargetedQuadConicWrongSense in
reformulation retargetedQuadConicWrongSense : maximum := by test_quadConic_retarget_sense

-- Every rejection preserves the ability to reuse the output and companion names.
reformulation lateProperty : source := by nlp
example : IsSmoothNLP lateProperty := lateProperty.isSmoothNLP

end
end MorewTest.Reformulation.TerminalEvidence
