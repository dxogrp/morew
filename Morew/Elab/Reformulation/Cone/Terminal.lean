/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Reformulation.Cone.Presentation
import Morew.Elab.Reformulation.Rows

/-! Allocate names and materialize a terminal cone form through the selected adapter. -/

namespace Morew.Elab.Reformulation.Cone

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def materializeTerminalConeForm (adapter : TerminalAdapter) (artifactStem : Name)
    (state : ReformState)
    (prepared : Morew.Elab.Cone.Terminal.Result) (preparedVars : Array Expr)
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
    let primitive ← Rows.storeCertificate (artifactStem.appendAfter "Certificate") primitive
      (candidates ++ [(`terminal_source, typed.canonical), (`terminal_target, targetProblem)])
    let mut binders := state.view.binders
    for i in [:prepared.auxiliaries.size] do
      let some name := allocation.findName? i
        | throwError "internal error: missing terminal auxiliary allocation"
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
          | throwError "internal error: missing terminal row allocation"
        rows := rows.push { name, proposition := (← `(True)).raw : Morew.Syntax.ConstraintView }
      else
        rows := rows.push state.view.constraints[origin]!
    let template := { state.view with binders, constraints := rows }
    let rendered ← problemViewFromExpression targetProblem template (recoverDefinitions := false)
    -- Prove agreement with reduced zero/negation definitions while retaining their display names.
    let normalizationLemmas := state.normalizationLemmas ++
      #[⟨mkCIdent ``sub_zero⟩, ⟨mkCIdent ``zero_sub⟩,
        ⟨mkCIdent ``sub_neg_eq_add⟩, ⟨mkCIdent ``zero_add⟩, ⟨mkCIdent ``neg_neg⟩]
    let view ← Presentation.normalizeRetainedView
      state.sourceName normalizationLemmas prepared template rendered
    let semantic ← exactExpressionSyntax targetProblem
    let formName ← mkAuxDeclName (kind := artifactStem.appendAfter "Form")
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
      normalizationLemmas
      checkpoint? := some { semantic, semanticAnchor := semantic, view }
      constraintSplices := prepared.replacedIndices.map fun index =>
        { index, count := (prepared.rowOrigins.filter (· == index)).size }
      terminalForm? := some (adapter, ← exactExpressionSyntax form)
      status := .terminal
    }

/-- Elaborate an objective certificate against its backend's expected type. -/
def elaborateObjectiveCertificate (provided : Term) (expected : Expr) : TermElabM Expr :=
  withRef provided do
    let proof ← elabTermEnsuringType provided expected
    synthesizeSyntheticMVarsNoPostponing
    if (← getThe Core.State).messages.hasErrors then throwAbortTerm
    return ← instantiateMVars proof

/-- Plan the complete exact conversion and request all generated local names.
Build the backend in the current section context before normalizing the objective. -/
def prepareTerminalConeForm
    (makeBackend : PresentationState → TermElabM Morew.Elab.Cone.Terminal.Backend)
    (adapter : TerminalAdapter) (artifactStem : Name) (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft := withRef step do
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => withoutErrToSorry do
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let backend ← makeBackend presentation
    let presentation ← Presentation.normalizeDirectPresentation backend presentation
    match ← Morew.Elab.Cone.Terminal.planWith backend presentation with
    | .error error => throwError "terminal {adapter.description} validation is uncertified: {error.reason}"
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
        requested := Name.mkSimple s!"{stem}_conic_{count}", ref := step }
  return {
    nameRequests
    materialize := materializeTerminalConeForm adapter artifactStem state prepared preparedVars
  }

end Morew.Elab.Reformulation.Cone
