import PTran.Reformulation.Presentation
import PTran.Conic.Basic

/-!
# Surface step validation and commitment

Bridge surface materialization to the checked typed runner before updating state.
-/

namespace PTran.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

private abbrev SurfaceMaterializerM :=
  StateT (Option SurfaceMaterialization) CommandElabM

private def validateTypedPrimitive (state : ReformState)
    (result : SurfaceStepResult) :
    CommandElabM (PTran.Elab.Reformulation.StepResult × Array Expr ×
      Option CheckedTerminalConicArtifact) :=
  runTermElabM fun sectionFVars => do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let next ← elabTerm result.semantic none
    let nextDomain ← elabTerm result.semanticDomainType none
    synthesizeSyntheticMVarsNoPostponing
    let next ← instantiateMVars next
    let nextDomain ← instantiateMVars nextDomain
    let current := typed.semantic
    let expectedValue := typed.semanticValueType
    let nextType ← whnf (← inferType next)
    unless nextType.getAppFn.isConstOf ``PTran.Problem &&
        nextType.getAppNumArgs == 2 do
      throwErrorAt result.semantic
        "a reformulation step produced a term that is not a `PTran.Problem`"
    unless ← isDefEq nextType.getAppArgs[0]! nextDomain do
      throwErrorAt result.semantic
        "a reformulation step reported the wrong decision-domain type"
    unless ← isDefEq nextType.getAppArgs[1]! expectedValue do
      throwErrorAt result.semantic
        "a reformulation step changed the objective value type"
    let expectedCertificate ← state.runner.relationType current next
    let primitiveProof ← elabTerm result.primitiveCertificate (some expectedCertificate)
    synthesizeSyntheticMVarsNoPostponing
    let primitiveProof ← instantiateMVars primitiveProof
    if primitiveProof.hasMVar then
      throwErrorAt result.primitiveCertificate
        "primitive reformulation certificate contains unresolved metavariables"
    let checkpoint := result.checkpoint?.getD state.checkpoint
    unless result.checkpoint?.isNone || result.removedConstraintNames.isEmpty do
      throwError "a new canonicalization checkpoint must start with no removed constraints"
    let nextCanonical ← canonicalTargetExpression state.sourceName checkpoint.semantic
      checkpoint.view result.removedConstraintNames result.semantic
      result.simplifyExpLogTerms
    let currentPresentation := typed.presentation
    let nextPresentation ←
      typedPresentationFromExpression nextCanonical result.view
    let normalization ←
      checkedPointwiseNormalization state.source next nextCanonical
        result.normalizationLemmas
    let presentationDelta ← presentationDeltaBetween currentPresentation
      nextPresentation normalization.objectiveEquality normalization.feasibleIff
      result.constraintSplices
    let updatedPresentation ← match currentPresentation.applyDelta presentationDelta with
      | .ok presentation => pure presentation
      | .error error =>
          throwError "invalid presentation delta produced by reformulation step: {repr error}"
    unless updatedPresentation.binders.size == nextPresentation.binders.size &&
        updatedPresentation.constraints.size == nextPresentation.constraints.size do
      throwError "presentation delta did not reproduce the next presentation shape"
    for index in [:nextPresentation.binders.size] do
      let actual := updatedPresentation.binders[index]!
      let expected := nextPresentation.binders[index]!
      unless sameUserName actual.name expected.name &&
          (← isDefEq actual.type expected.type) do
        throwError "presentation delta did not reproduce decision binder {index}"
    unless ← isDefEq updatedPresentation.objective nextPresentation.objective do
      throwError "presentation delta did not reproduce the next objective"
    for index in [:nextPresentation.constraints.size] do
      let actual := updatedPresentation.constraints[index]!
      let expected := nextPresentation.constraints[index]!
      unless sameUserName actual.name expected.name &&
          (← isDefEq actual.predicate expected.predicate) do
        throwError "presentation delta did not reproduce constraint {index}"
    let typedResult : PTran.Elab.Reformulation.StepResult := {
      nextSemantic := next
      primitiveCertificate := primitiveProof
      presentationDelta
      status := result.status
      companions := result.companions
    }
    let expectedCanonical ← updatedPresentation.canonicalProblem
    unless ← isDefEq normalization.canonical expectedCanonical do
      throwError "checked normalization does not target the presentation delta"
    let terminalConic? ← result.terminalForm?.mapM fun (formSyntax : TSyntax `term) => do
      unless result.status == .terminal do
        throwErrorAt formSyntax "a conic form requires a terminal result"
      let form ← elabTerm formSyntax none
      synthesizeSyntheticMVarsNoPostponing
      let form ← instantiateMVars form
      if form.hasMVar then
        throwErrorAt formSyntax "terminal conic form contains unresolved metavariables"
      let type ← whnf (← inferType form)
      unless type.isAppOfArity ``PTran.Conic.Form 5 do
        throwErrorAt formSyntax "terminal evidence is not a Conic.Form"
      unless ← isDefEq type.getAppArgs.back! expectedCanonical do
        throwErrorAt formSyntax "terminal conic form does not represent the final canonical problem"
      -- Use the form's stored instances even when finiteness was available
      -- only inside a source constraint during planning.
      let data ← mkProjection form `data
      let sense ← mkProjection data `sense
      let expectedSense := match nextPresentation.sense with
        | .minimize => mkConst ``PTran.ObjectiveSense.minimize
        | .maximize => mkConst ``PTran.ObjectiveSense.maximize
      unless ← isDefEq sense expectedSense do
        throwErrorAt formSyntax "terminal conic form has the wrong objective sense"
      checkWithKernel form
      pure { form, ref := formSyntax.raw : CheckedTerminalConicArtifact }
    pure (typedResult, sectionFVars, terminalConic?)

private def typedStepPlan (state : ReformState) (draft : SurfaceStepDraft) :
    PTran.Elab.Reformulation.StepPlan SurfaceMaterializerM := {
  nameRequests := draft.nameRequests
  materialize := fun allocation _ => do
    let surface ← draft.materialize allocation
    let (result, sectionFVars, terminalConic?) ←
      validateTypedPrimitive state surface
    pure (result, some { surface, sectionFVars, terminalConic? })
}

private def reportNamePreflightError {α}
    (error : PTran.Elab.Reformulation.NamePreflightError) :
    CommandElabM α := do
  match error with
  | .duplicateRequestId request =>
      throwErrorAt request.ref "duplicate internal name-request id `{request.id}`"
  | .collision request occupied =>
      let name := occupied.eraseMacroScopes
      match request.kind with
      | .explicitDecisionBinder | .inferredDecisionBinder =>
          throwErrorAt request.ref "decision variable `{name}` already exists"
      | .explicitConstraintLabel =>
          throwErrorAt request.ref "constraint name `{name}` already exists"
      | .fixedPublicDefault =>
          throwErrorAt request.ref
            "generated constraint name `{name}` already exists; use `as <label>` to choose a different constraint label"
      | .generatedBinderFamily | .generatedRowFamily =>
          throwErrorAt request.ref
            "internal error: generated name `{name}` was not freshened"

/-- Preflight and validate a surface step, retaining its checked materialization. -/
def runTypedStepPlan (state : ReformState) (draft : SurfaceStepDraft) :
    CommandElabM (PTran.Elab.Reformulation.StepResult ×
      SurfaceMaterialization) := do
  let plan := typedStepPlan state draft
  let active := state.typed.presentation.nameInventory
  let (outcome, materialization?) ← (plan.run active).run.run none
  let result ← match outcome with
    | .ok result => pure result
    | .error error => reportNamePreflightError error
  let some materialization := materialization?
    | throwError "internal error: typed step produced no surface materialization"
  pure (result, materialization)

/-- Commit a validated typed step and update its surface representation. -/
def commitSurfaceStep (state : ReformState)
    (result : PTran.Elab.Reformulation.StepResult)
    (materialization : SurfaceMaterialization) : CommandElabM ReformState := do
  let (committed, sectionFVars) ← runTermElabM fun sectionFVars => do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let result := result.replaceFVars materialization.sectionFVars sectionFVars
    let committed ← typed.commit state.runner result
    pure (committed, sectionFVars)
  let typed ← match committed with
    | .ok typed => pure typed
    | .error error =>
        throwError "invalid presentation delta produced by reformulation step: {repr error}"
  let surface := materialization.surface
  let certificateSyntax ← liftMacroM <|
    certificateTransTerm state.runner state.certificateSyntax
      surface.primitiveCertificate
  pure {
    state with
    typed
    sectionFVars
    view := surface.view
    semantic := surface.semantic
    semanticDomainType := surface.semanticDomainType
    checkpoint := surface.checkpoint?.getD state.checkpoint
    certificateSyntax
    simplifyExpLogTerms := surface.simplifyExpLogTerms
    hasSubstitution := surface.hasSubstitution
    removedConstraintNames := surface.removedConstraintNames
    normalizationLemmas := surface.normalizationLemmas
    terminalConic? := materialization.terminalConic?.map
      (·.replaceFVars materialization.sectionFVars sectionFVars)
  }

end PTran.Reformulation.Internal
