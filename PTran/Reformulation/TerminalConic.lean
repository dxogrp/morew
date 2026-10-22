import PTran.Elab.Conic.Terminal
import PTran.Reformulation.Conic

/-!
# Terminal conic validation

Bare `conic` certifies the entire final problem. It preserves already-conic
presentation groups, lowers nonlinear conjunction leaves exactly, and retains
the structural form for emission beside the named target. All generated local
names are allocated together before the terminal result is materialized.
-/

namespace PTran.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open PTran.Elab.Reformulation

private def terminalStem (state : ReformState) (origin : Nat) : CommandElabM String := do
  let name := state.view.constraints[origin]!.name.eraseMacroScopes
  let .str _ stem := name
    | throwError "cannot derive a generated-name family from constraint `{name}`"
  return stem

private def materializeTerminalConic (state : ReformState)
    (prepared : PTran.Elab.Conic.Terminal.Result) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared := prepared.replaceFVars preparedVars sectionFVars
    let targetProblem ← prepared.presentation.canonicalProblem
    let exact ← mkAppM ``PTran.GlobalEquivalence.trans
      #[typed.normalization.equivalence, prepared.equivalence]
    let primitive ← state.runner.liftEquivalence exact
    let candidates := (typed.presentation.constraints ++ prepared.presentation.constraints).toList
      |>.zipIdx |>.map fun (row, index) => (Name.mkSimple s!"terminal_row_{index}", row.predicate)
    let primitive ← shareConicCertificate (← instantiateMVars primitive)
      (candidates ++ [(`terminal_source, typed.canonical), (`terminal_target, targetProblem)])
    checkWithKernel primitive
    let primitiveName ← mkAuxDeclName (kind := `_terminalConicCertificate)
    let primitive ← mkAuxDefinitionFor primitiveName primitive (zetaDelta := true)
      (compile := false)
    modifyEnv (addNoncomputable · primitiveName)
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
        rows := rows.push { name, proposition := (← `(True)).raw : PTran.Syntax.ConstraintView }
      else
        rows := rows.push state.view.constraints[origin]!
    let template := { state.view with binders, constraints := rows }
    let rendered ← problemViewFromExpression targetProblem template
    let view := { template with constraints := rows.mapIdx fun i row =>
      if prepared.replacedIndices.contains prepared.rowOrigins[i]! then
        rendered.constraints[i]! else row }
    let semantic ← exactExpressionSyntax targetProblem
    let formName ← mkAuxDeclName (kind := `_terminalConicForm)
    let form ← mkAuxDefinitionFor formName prepared.form (zetaDelta := true) (compile := false)
    modifyEnv (addNoncomputable · formName)
    return {
      view
      semantic
      semanticDomainType := ← exactExpressionSyntax prepared.presentation.domainType
      primitiveCertificate := ← exactExpressionSyntax primitive
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      removedConstraintNames := {}
      normalizationLemmas := state.normalizationLemmas
      checkpoint? := some { semantic, view }
      constraintSplices := prepared.replacedIndices.map fun index =>
        { index, count := (prepared.rowOrigins.filter (· == index)).size }
      terminalForm? := some (← exactExpressionSyntax form)
      status := .terminal
    }

/-- Plan the complete exact conversion and request all generated local names. -/
def prepareTerminalConic (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft := withRef step do
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    match ← PTran.Elab.Conic.Terminal.plan presentation with
    | .error error => throwError "terminal conic validation is uncertified: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  let mut nameRequests := #[]
  for i in [:prepared.auxiliaries.size] do
    let stem ← terminalStem state prepared.auxiliaries[i]!.1
    nameRequests := nameRequests.push {
      id := i, kind := .generatedBinderFamily
      requested := Name.mkSimple (stem ++ "_aux"), ref := step }
  let mut counts := Array.replicate state.view.constraints.size 0
  for i in [:prepared.rowOrigins.size] do
    let origin := prepared.rowOrigins[i]!
    if prepared.replacedIndices.contains origin then
      let count := counts[origin]! + 1
      counts := counts.set! origin count
      let stem ← terminalStem state origin
      nameRequests := nameRequests.push {
        id := prepared.auxiliaries.size + i, kind := .generatedRowFamily
        requested := Name.mkSimple s!"{stem}_conic_{count}", ref := step }
  return { nameRequests, materialize := materializeTerminalConic state prepared preparedVars }

end PTran.Reformulation.Internal
