import PTran.Reformulation.ObjectiveBound
import PTran.Reformulation.Conic
import PTran.Reformulation.StepRunner
import PTran.Reformulation.Substitution
import PTran.Reformulation.Syntax
import Lean.Elab.MutualDef

/-!
# Reformulation command

This module implements the small, proof-producing transformation language used
by PTran's first release.  A reformulation command declares both the transformed
problem and a `GlobalEquivalence` certificate.  Convexity is deliberately not
part of either the command or the generated proof.
-/

namespace PTran

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser
open PTran.Reformulation.Internal

private def outputDeclName (ident : TSyntax `ident) : CommandElabM Name := do
  let shortName := ident.getId
  let view := extractMacroScopes shortName
  let name := view.name
  if name == `_root_ then
    throwErrorAt ident
      "invalid declaration name `_root_`, `_root_` is a prefix used to refer to the root namespace"
  if (`_root_).isPrefixOf name then
    pure { view with name := name.replacePrefix `_root_ Name.anonymous }.review
  else
    pure ((← getCurrNamespace) ++ shortName)

private def rootIdentFrom (ref : Syntax) (name : Name) : TSyntax `ident :=
  ⟨mkIdentFrom ref (`_root_ ++ name)⟩

private def ensureFreshOutput (ref : Syntax) (name : Name) : CommandElabM Unit :=
  withRef ref do
    checkIfShadowingStructureField name
    checkNotAlreadyDeclared name

private def withDeclarationTransaction (action : CommandElabM Unit) : CommandElabM Unit := do
  let savedState ← get
  set { savedState with messages := .empty }
  try
    action
    let resultingState ← get
    let messages := savedState.messages ++ resultingState.messages
    if resultingState.messages.hasErrors then
      set { savedState with messages }
    else
      set { resultingState with messages }
  catch exception =>
    let generatedMessages := (← get).messages
    set { savedState with messages := savedState.messages ++ generatedMessages }
    throw exception

private def elabSemanticTarget (target : TSyntax `ident)
    (sourceName : Name) (sourceTerm : TSyntax `term)
    (sourceView : PTran.Syntax.ProblemView)
    (removedConstraintNames : NameSet) (semantic : TSyntax `term)
    (simplifyExpLogTerms : Bool) : CommandElabM Unit := do
  let scope ← getScope
  withExporting (isExporting := scope.isPublic) do
  withInitQuotContext (some (hash #[target.getId])) do
    runTermElabM fun sectionVars => do
      let expression ← canonicalTargetExpression sourceName sourceTerm sourceView
        removedConstraintNames semantic simplifyExpLogTerms
      if expression.hasMVar then
        throwErrorAt semantic "term contains unresolved metavariables"
      let definition ← `(Parser.Command.definition|
        def $target := $(← Term.exprToSyntax expression))
      let view := Command.mkDefViewOfDef
        { computeKind := .noncomputable } definition
      Term.elabMutualDef sectionVars scope #[view]

private inductive RawDeclarationResult where
  | success
  | failed
  | retryWithSemanticTarget (messages : MessageLog)

private inductive RawDeclarationStage where
  | target
  | certificate
  | alias
  deriving BEq

/-- Try the source-aligned target first. Re-elaborating presentation syntax can
omit implicit data or select different instances, so target and certificate
failures retry the checked semantic target. Retain the original diagnostics if
that retry also fails. Alias failures and internal exceptions are not retried. -/
private def tryRawDeclarations (targetCommand certificateCommand : Syntax)
    (aliasCommand? : Option Syntax) : CommandElabM RawDeclarationResult := do
  let savedState ← get
  set { savedState with messages := .empty }
  let mut stage := RawDeclarationStage.target
  try
    elabCommand targetCommand
    if (← get).messages.hasErrors then
      let messages := (← get).messages
      set savedState
      return .retryWithSemanticTarget messages

    stage := .certificate
    elabCommand certificateCommand
    if (← get).messages.hasErrors then
      let messages := (← get).messages
      set savedState
      return .retryWithSemanticTarget messages

    if let some aliasCommand := aliasCommand? then
      stage := .alias
      elabCommand aliasCommand
      if (← get).messages.hasErrors then
        let resultingState ← get
        set { resultingState with
          messages := savedState.messages ++ resultingState.messages }
        return .failed

    let resultingState ← get
    set { resultingState with
      messages := savedState.messages ++ resultingState.messages }
    pure .success
  catch exception =>
    let resultingState ← get
    match exception with
    | .error _ _ =>
        if stage == .target || stage == .certificate then do
          logException exception
          let messages := (← get).messages
          set savedState
          pure (.retryWithSemanticTarget messages)
        else do
          set { savedState with
            messages := savedState.messages ++ resultingState.messages }
          throw exception
    | .internal _ _ =>
        set savedState
        throw exception

private def emitCompanionDeclaration
    (request : PTran.Elab.Reformulation.CompanionRequest)
    (sectionFVars : Array Expr) :
    CommandElabM Unit := do
  let (typeSyntax, valueSyntax) ← runTermElabM fun currentSectionFVars => do
    let request := request.replaceFVars sectionFVars currentSectionFVars
    let typeSyntax ← exactExpressionSyntax request.type
    let valueSyntax ← exactExpressionSyntax request.value
    pure (typeSyntax, valueSyntax)
  let declarationIdent := rootIdentFrom request.ref request.name
  let command ← liftMacroM `(command|
    noncomputable def $declarationIdent : $typeSyntax := $valueSyntax)
  elabCommand command

private def elabReformulationCore : CommandElab := fun stx => do
  let `(reformulation $targetName:ident : $sourceIdent:ident
      $[certificate $aliasName:ident]? := by $steps:reformulationStep*) := stx
    | throwUnsupportedSyntax

  let targetDeclName ← outputDeclName targetName
  let certificateDeclName := targetDeclName ++ `equivalence
  let aliasDeclName? ← aliasName.mapM outputDeclName
  if let some aliasDeclName := aliasDeclName? then
    if aliasDeclName == targetDeclName then
      throwErrorAt aliasName.get!
        "certificate alias names the same declaration as the reformulation target"
    if aliasDeclName == certificateDeclName then
      throwErrorAt aliasName.get!
        "certificate alias names the same declaration as the canonical certificate"
  let targetDeclIdent := rootIdentFrom targetName targetDeclName
  let certificateDeclIdent := rootIdentFrom targetName certificateDeclName
  let aliasDeclIdent? := match aliasName, aliasDeclName? with
    | some ref, some name => some (rootIdentFrom ref name)
    | _, _ => none

  let sourceName ← resolveGlobalConstNoOverload sourceIdent
  let env ← getEnv
  let some sourceView := PTran.Syntax.getProblemView? env sourceName
    | throwErrorAt sourceIdent
        "declaration `{sourceName}` has no registered problem presentation"

  let sourceTerm : TSyntax `term :=
    ⟨(rootIdentFrom sourceIdent sourceName).raw⟩
  let problemTypes ← problemTypeSyntax sourceTerm
  let runner := globalEquivalenceRunner
  let initialCertificateSyntax ← liftMacroM <|
    certificateReflTerm runner sourceTerm
  let (typed, sectionFVars) ← runTermElabM fun sectionFVars => do
    let source ← elabTerm sourceTerm none
    synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let canonical ← canonicalTargetExpression sourceName sourceTerm sourceView
      {} sourceTerm false
    let presentation ← typedPresentationFromExpression canonical sourceView
    let normalization ← checkedPointwiseNormalization sourceTerm source canonical #[]
    let accumulatedCertificate ← runner.reflexivity source
    synthesizeSyntheticMVarsNoPostponing
    let accumulatedCertificate ← instantiateMVars accumulatedCertificate
    let typed : PTran.Elab.Reformulation.RunnerState := {
      semantic := source
      canonical
      semanticDomainType := presentation.domainType
      semanticValueType := presentation.valueType
      presentation
      accumulatedCertificate
      normalization
    }
    pure (typed, sectionFVars)
  let mut state : ReformState := {
    typed
    sectionFVars
    view := sourceView
    semantic := sourceTerm
    semanticDomainType := problemTypes.domain
    semanticValueType := problemTypes.value
    presentationValueType := problemTypes.presentationValue
    certificateSyntax := initialCertificateSyntax
    source := sourceTerm
    sourceName
    checkpoint := { semantic := sourceTerm, view := sourceView }
    runner
  }

  for step in steps do
    if state.typed.status == .terminal then
      throwErrorAt step "cannot apply a reformulation step after a terminal step"
    let draft ← match step with
      | `(reformulationStep| substitute $oldName:ident := $replacement:term
          $[using $provided:term]?) =>
          prepareSubstitution state step oldName replacement provided
      | `(reformulationStep| epigraph $binder:ident $[as $label:ident]?) =>
          prepareObjectiveBound state step binder label .minimize
      | `(reformulationStep| hypograph $binder:ident $[as $label:ident]?) =>
          prepareObjectiveBound state step binder label .maximize
      | `(reformulationStep| conic at $selector:ident $[using $rule:term]?) =>
          prepareConic state step selector rule
      | _ => throwUnsupportedSyntax
    let (result, materialization) ← runTypedStepPlan state draft
    state ← commitSurfaceStep state result materialization

  let mut outputRequests :
      Array PTran.Elab.Reformulation.DeclarationNameRequest := #[
    { name := targetDeclName, ref := targetName.raw },
    { name := certificateDeclName, ref := targetName.raw }
  ]
  if let some aliasDeclName := aliasDeclName? then
    outputRequests := outputRequests.push {
      name := aliasDeclName
      ref := aliasName.get!.raw
    }
  for companion in state.typed.companions do
    outputRequests := outputRequests.push companion.nameRequest
  match PTran.Elab.Reformulation.preflightDeclarationNames
      (← getEnv) outputRequests with
  | .ok _ => pure ()
  | .error (.alreadyDeclared request) =>
      ensureFreshOutput request.ref request.name
  | .error (.duplicate request) =>
      throwErrorAt request.ref
        "duplicate generated declaration name `{request.name}`"
  for request in outputRequests do
    ensureFreshOutput request.ref request.name

  withDeclarationTransaction do
    let stableSemantic ← stabilizeTerm state.semantic
    if (← get).messages.hasErrors then
      return
    runTermElabM fun sectionFVars => do
      let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
      let finalProof ← typed.finalCertificate state.runner
      synthesizeSyntheticMVarsNoPostponing
      let finalProof ← instantiateMVars finalProof
      if finalProof.hasMVar then
        throwError "final reformulation certificate contains unresolved metavariables"
      check finalProof
    let stableEquivalenceProof := state.certificateSyntax

    let targetTerm ← liftMacroM <| state.view.toTermSyntax
    let targetCommand ← liftMacroM `(
      command| noncomputable def $targetDeclIdent := $targetTerm)

    let normalizationLemmas ← liftMacroM <|
      normalizationSimpLemmas sourceTerm state.normalizationLemmas
    let targetSimp ← liftMacroM `(
      Lean.Parser.Tactic.simpLemma| $targetDeclIdent:term)
    let normalizationLemmas := normalizationLemmas.push targetSimp
    let normalizationEquivalence ← liftMacroM `(
      PTran.pointwiseEquivalence $stableSemantic $targetDeclIdent
        (fun _ => by
          simp only [$[$normalizationLemmas],*] <;> rfl)
        (fun _ => by
          simp only [$[$normalizationLemmas],*] <;> rfl))
    let normalization ← liftMacroM <|
      liftCertificateEquivalence state.runner normalizationEquivalence
    let equivalenceProof ← liftMacroM <|
      certificateTransTerm state.runner stableEquivalenceProof normalization
    let relation ← liftMacroM <|
      certificateRelationTerm state.runner sourceTerm ⟨targetDeclIdent.raw⟩
    let certificateCommand ← liftMacroM `(command|
      noncomputable def $certificateDeclIdent :
          $relation := by
        exact $equivalenceProof)
    let aliasCommand? ← aliasDeclIdent?.mapM fun aliasDeclIdent =>
      liftMacroM `(command|
        noncomputable abbrev $aliasDeclIdent : $relation :=
          $certificateDeclIdent)

    let elabCanonicalDeclarations : CommandElabM Unit := do
      elabSemanticTarget targetDeclIdent sourceName state.checkpoint.semantic state.checkpoint.view
        state.removedConstraintNames stableSemantic state.simplifyExpLogTerms
      unless (← get).messages.hasErrors do
        elabCommand certificateCommand
        unless (← get).messages.hasErrors do
          if let some aliasCommand := aliasCommand? then
            elabCommand aliasCommand

    let emitted ← if state.hasSubstitution then do
        elabCanonicalDeclarations
        pure !(← get).messages.hasErrors
      else
        match ← tryRawDeclarations targetCommand certificateCommand aliasCommand? with
        | .success => pure true
        | .failed => pure false
        | .retryWithSemanticTarget rawMessages =>
            try
              elabCanonicalDeclarations
              let emitted := !(← get).messages.hasErrors
              unless emitted do
                modify fun state => { state with messages := state.messages ++ rawMessages }
              pure emitted
            catch exception =>
              modify fun state => { state with messages := state.messages ++ rawMessages }
              throw exception
    if emitted then
      for companion in state.typed.companions do
        unless (← get).messages.hasErrors do
          emitCompanionDeclaration companion state.sectionFVars
      unless (← get).messages.hasErrors do
        refreshProblemView targetDeclName state.view

/-- Elaborate a reformulation declaration and emit the transformed problem and
its composed global-equivalence certificate.  Planning, typed step validation,
declaration emission, companions, and metadata registration share one rollback
boundary. -/
@[command_elab reformulationCmd]
def elabReformulation : CommandElab := fun stx =>
  withDeclarationTransaction (elabReformulationCore stx)

end PTran
