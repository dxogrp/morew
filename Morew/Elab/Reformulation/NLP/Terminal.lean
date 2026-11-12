/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.NLP.Terminal
import Morew.Elab.Reformulation.Rows

/-! Apply exact bound rewrites and certify the objective and residuals on a common
open domain containing the feasible set. Emit `equiv`, `nlpForm`, and `isSmoothNLP`.
Domain inference leaves feasibility unchanged.

Store scalar residuals `a - b` with upper, lower, or fixed zero bounds; retain grouped
conjunctions and finite families for display. Families support symbolic and zero
dimensions, but not general quantifiers. Maximization retains `OrderDual ℝ` and
records `maximize` in the form.

This terminal step allocates names and emits declarations and metadata atomically. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def terminalNLPAdapter : TerminalAdapter :=
  TerminalAdapter.ofForm ``Morew.NLP.Form
    (formDescription := "NLP.Form") (description := "smooth NLP")
    (formSuffix := `nlpForm) (propertySuffix := `isSmoothNLP)

private def materializeTerminalNLP (state : ReformState)
    (prepared : Morew.Elab.NLP.Terminal.Result) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared := prepared.replaceFVars preparedVars sectionFVars
    let targetProblem ← prepared.presentation.canonicalProblem
    let exact ← mkAppM ``Morew.GlobalEquiv.trans
      #[typed.normalization.equiv, prepared.equiv]
    let primitive ← state.runner.liftEquiv exact
    let candidates := (typed.presentation.constraints ++ prepared.presentation.constraints).toList
      |>.zipIdx |>.map fun (row, index) => (Name.mkSimple s!"terminal_row_{index}", row.predicate)
    let primitive ← Rows.storeCertificate `_terminalNLPCertificate primitive
      (candidates ++ [(`terminal_source, typed.canonical), (`terminal_target, targetProblem)])
    let mut binders := state.view.binders
    for i in [:prepared.auxiliaries.size] do
      let some name := allocation.findName? i
        | throwError "internal error: missing terminal NLP auxiliary allocation"
      let name ← withFreshMacroScope do MonadQuotation.addMacroScope name
      binders := binders.push {
        name
        typeSyntax := ← presentationTypeSyntax prepared.auxiliaries[i]!.2
      }
    let mut rows := #[]
    for i in [:prepared.rowOrigins.size] do
      let origin := prepared.rowOrigins[i]!
      if prepared.replacedIndices.contains origin then
        let some name := allocation.findName? (prepared.auxiliaries.size + i)
          | throwError "internal error: missing terminal NLP row allocation"
        rows := rows.push { name, proposition := (← `(True)).raw : Morew.Syntax.ConstraintView }
      else
        rows := rows.push state.view.constraints[origin]!
    let template := { state.view with binders, constraints := rows }
    let rendered ← problemViewFromExpression targetProblem template (recoverDefinitions := false)
    -- Retain source binding identities; use planner expressions for generated rows.
    let constraints := template.constraints.mapIdx fun i row =>
      if prepared.replacedIndices.contains prepared.rowOrigins[i]! then
        rendered.constraints[i]!
      else row
    let view := { template with constraints }
    let semantic ← exactExpressionSyntax targetProblem
    let formName ← mkAuxDeclName (kind := `_terminalNLPForm)
    let form ← mkAuxDefinitionFor formName prepared.form (zetaDelta := true) (compile := false)
    modifyEnv (addNoncomputable · formName)
    return {
      view
      semantic
      semanticDomainType := ← exactExpressionSyntax prepared.presentation.domainType
      primitiveCertificate := ← exactExpressionSyntax primitive
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      liveCheckpointRows := Array.range view.constraints.size
      removedCheckpointRows := {}
      normalizationLemmas := state.normalizationLemmas
      checkpoint? := some { semantic, semanticAnchor := semantic, view }
      constraintSplices := prepared.replacedIndices.map fun index =>
        { index, count := (prepared.rowOrigins.filter (· == index)).size }
      terminalForm? := some (terminalNLPAdapter, ← exactExpressionSyntax form)
      status := .terminal
    }

/-- Certify the whole smooth problem and request all generated local names. -/
def prepareTerminalNLP (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft := withRef step do
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let reduce := fun expression => dsimpPreservingProofLets expression (preserveOperations := false)
    match ← Morew.Elab.NLP.Terminal.plan presentation (some reduce) with
    | .error error => throwError error.reason
    | .ok result => pure (result, sectionFVars)
  let mut nameRequests := #[]
  for i in [:prepared.auxiliaries.size] do
    let stem ← Rows.terminalStem state prepared.auxiliaries[i]!.1
    nameRequests := nameRequests.push {
      id := i, kind := .generatedBinderFamily
      requested := Name.mkSimple (stem ++ "_aux"), ref := step }
  let mut counts := Array.replicate state.view.constraints.size 0
  for i in [:prepared.rowOrigins.size] do
    let origin := prepared.rowOrigins[i]!
    if prepared.replacedIndices.contains origin then
      let count := counts[origin]! + 1
      counts := counts.set! origin count
      let stem ← Rows.terminalStem state origin
      nameRequests := nameRequests.push {
        id := prepared.auxiliaries.size + i, kind := .generatedRowFamily
        requested := Name.mkSimple s!"{stem}_nlp_{count}", ref := step }
  return { nameRequests, materialize := materializeTerminalNLP state prepared preparedVars }

@[morew_reformulation_step Morew.nlpStep]
private def elabNLP : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| nlp) => prepareTerminalNLP state step
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
