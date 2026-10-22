import PTran.Reformulation.ObjectiveBound
import PTran.Reformulation.Conic
import PTran.Reformulation.TerminalConic
import PTran.Reformulation.StepRunner
import PTran.Reformulation.Substitution
import PTran.Reformulation.Syntax
import Lean.Elab.MutualDef

/-!
# Reformulation command

This module implements the small, proof-producing transformation language used
by PTran's first release.  A reformulation command declares both the transformed
problem and a `GlobalEquivalence` certificate. Terminal conic validation also
retains a structural form and a proof of conic representability.
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
private def tryRawDeclarations (targetCommand : Syntax)
    (emitCertificate emitAlias : CommandElabM Unit) : CommandElabM RawDeclarationResult := do
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
    emitCertificate
    if (← get).messages.hasErrors then
      let messages := (← get).messages
      set savedState
      return .retryWithSemanticTarget messages

    stage := .alias
    emitAlias
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

-- Applied and terminal output use the already checked canonical expression. In particular,
-- the explicit objective-value annotation must retain OrderDual for maxima.
private def emitCheckedTarget (target : TSyntax `ident) (state : ReformState) :
    CommandElabM Unit := do
  let scope ← getScope
  withExporting (isExporting := scope.isPublic) do
  withInitQuotContext (some (hash #[target.getId])) do
    runTermElabM fun sectionVars => do
      let typed := state.typed.replaceFVars state.sectionFVars sectionVars
      let type ← mkAppM ``PTran.Problem
        #[typed.presentation.domainType, typed.semanticValueType]
      let definition ← `(Parser.Command.definition|
        def $target : $(← exactExpressionSyntax type) :=
          $(← exactExpressionSyntax typed.canonical))
      let view := Command.mkDefViewOfDef { computeKind := .noncomputable } definition
      Term.elabMutualDef sectionVars scope #[view]

/-- Recover the emitted declaration's actual parameter application. Equality
can ignore proof arguments, so recover any remaining evidence from the context
and recheck the completed application. -/
private def recoverDeclarationApplication (name : Name) (expected : Expr)
    (matchType : Bool := false) : TermElabM Expr := do
  let declaration ← mkConstWithFreshMVarLevels name
  let (arguments, _, _) ← forallMetaTelescope (← inferType declaration)
  let application := mkAppN declaration arguments
  let actual ← if matchType then inferType application else pure application
  unless ← isDefEq actual expected do
    throwError "emitted declaration `{name}` does not match its checked expression"
  for argument in arguments do
    let argument ← instantiateMVars argument
    if let .mvar id := argument then
      -- Proof irrelevance may hide a data dependency from unification. Prefer
      -- the section parameter that Lean generalized under this binder name;
      -- choosing an arbitrary same-typed local would add unrelated parameters
      -- to the generated certificate and change its displayed endpoint.
      let binderName := (← id.getDecl).userName
      let candidates := (← getLCtx).decls.toArray.filterMap fun declaration? => do
        let declaration ← declaration?
        if sameUserName declaration.userName binderName then
          some declaration.toExpr
        else none
      if candidates.size == 1 then
        let candidate := candidates[0]!
        if ← isDefEq (← id.getType) (← inferType candidate) then
          id.assign candidate
          continue
      try
        id.assign (← synthInstance (← id.getType))
      catch _ =>
        if ← isProp (← id.getType) then
          id.assumption
  let application ← instantiateMVars application
  if application.hasMVar then
    throwError "parameters of emitted declaration `{name}` could not be recovered"
  let actual ← if matchType then inferType application else pure application
  unless ← isDefEq actual expected do
    throwError "recovered parameters of `{name}` changed its checked expression"
  pure application

private def emitTerminalArtifacts (targetName : Name) (state : ReformState)
    (artifact : CheckedTerminalConicArtifact) : CommandElabM Unit := do
  let scope ← getScope
  withExporting (isExporting := scope.isPublic) do
  withInitQuotContext (some (hash #[targetName])) do
    runTermElabM fun sectionVars => do
      let artifact := artifact.replaceFVars state.sectionFVars sectionVars
      let typed := state.typed.replaceFVars state.sectionFVars sectionVars
      let target ← recoverDeclarationApplication targetName typed.canonical
      let formType ← whnf (← inferType artifact.form)
      let formType := mkAppN formType.getAppFn
        (formType.getAppArgs.set! (formType.getAppNumArgs - 1) target)
      unless ← isDefEq (← inferType artifact.form) formType do
        throwErrorAt artifact.ref "the checked conic form does not represent the emitted target"
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        checkWithKernel artifact.form
      let formIdent := rootIdentFrom artifact.ref (targetName ++ `conicForm)
      let propertyIdent := rootIdentFrom artifact.ref (targetName ++ `isConic)
      let formDefinition ← `(Parser.Command.definition|
        def $formIdent : $(← exactExpressionSyntax formType) :=
          $(← exactExpressionSyntax artifact.form))
      Term.elabMutualDef sectionVars scope #[
        Command.mkDefViewOfDef { computeKind := .noncomputable } formDefinition]
      -- Elaborate both artifacts in the same section context. Lean does not
      -- permit mixing a noncomputable data definition and a theorem in one
      -- mutual group, so instantiate the newly declared form explicitly.
      let namedForm ← recoverDeclarationApplication (targetName ++ `conicForm) formType true
      -- The form already carries its canonical instances. Source-local finite
      -- evidence need not be available to typeclass search at emission time.
      let namedFormType ← whnf (← inferType namedForm)
      let property := mkAppN
        (mkConst ``PTran.Conic.Form.isConic namedFormType.getAppFn.constLevels!)
        (namedFormType.getAppArgs ++ #[namedForm])
      let propertyType ← inferType property
      let propertyDefinition ← `(Parser.Command.theorem|
        theorem $propertyIdent : $(← exactExpressionSyntax propertyType) :=
          $(← exactExpressionSyntax property))
      -- Source-domain hypotheses can be necessary for equivalence but absent
      -- from the final form. Keep the proof's complete dependency closure and
      -- explicitly omit unused instances, which Lean otherwise adds automatically.
      let used ←
        (Lean.collectFVars (Lean.collectFVars {} propertyType) property).addDependencies
      let mut propertyScope := { scope with includedVars := {} }
      for (name, sectionVar) in (← read).sectionFVars do
        if used.fvarSet.contains sectionVar.fvarId! then
          propertyScope := { propertyScope with includedVars := propertyScope.includedVars.insert name }
        else if (← sectionVar.fvarId!.getDecl).binderInfo.isInstImplicit then
          propertyScope := { propertyScope with omittedVars := propertyScope.omittedVars.insert name }
      Term.elabMutualDef sectionVars propertyScope
        #[Command.mkDefViewOfTheorem {} propertyDefinition]

private def elabReformulationCore : CommandElab := fun stx => do
  let (targetName, inputTerm, instantiatedSource, aliasName, steps) ← match stx with
    | `(reformulation $targetName:ident : $sourceIdent:ident
        $[certificate $aliasName:ident]? := by $steps:reformulationStep*) => do
        let sourceName ← resolveGlobalConstNoOverload sourceIdent
        pure (targetName, ⟨(rootIdentFrom sourceIdent sourceName).raw⟩, false, aliasName, steps)
    | `(reformulation $targetName:ident : ($sourceTerm:term)
        $[certificate $aliasName:ident]? := by $steps:reformulationStep*) =>
        pure (targetName, sourceTerm, true, aliasName, steps)
    | _ => throwUnsupportedSyntax

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

  let runner := globalEquivalenceRunner
  let (sourceName, sourceTerm, sourceView, problemTypes, typed, sectionFVars,
      usedSourceParameterNames) ← runTermElabM fun sectionFVars => withRef inputTerm do
    let source ← elabTerm inputTerm none
    synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    if source.hasMVar then
      throwError "reformulation source contains unresolved metavariables"
    let .const sourceName _ := source.consumeMData.getAppFn
      | throwError "reformulation source must be an application of a registered problem declaration"
    let some template := PTran.Syntax.getProblemView? (← getEnv) sourceName
      | throwError "declaration `{sourceName}` has no registered problem presentation"
    let problemTypes ← problemTypeSyntaxFromExpression source
    let sourceType ← whnf (← inferType source)
    let mut usedSourceParameterNames := #[]
    if instantiatedSource then
      let dependencies ← (Lean.collectFVars {} source).addDependencies
      for id in dependencies.fvarSet.toArray do
        let name := (← id.getDecl).userName.eraseMacroScopes
        if template.binders.any (sameUserName ·.name name) then
          throwError "source parameter `{name}` conflicts with a decision variable; rename the outer parameter"
        unless usedSourceParameterNames.contains name do
          usedSourceParameterNames := usedSourceParameterNames.push name
    let canonical ← canonicalTargetExpressionFromExpressions sourceName source template
      {} source false
    let sourceView ← if instantiatedSource then
        problemViewFromExpression canonical template true
      else pure template
    let presentation ← typedPresentationFromExpression canonical sourceView
    let normalization ← checkedPointwiseNormalization sourceName source canonical #[]
    let accumulatedCertificate ← runner.reflexivity source
    synthesizeSyntheticMVarsNoPostponing
    let accumulatedCertificate ← instantiateMVars accumulatedCertificate
    let typed : PTran.Elab.Reformulation.RunnerState := {
      semantic := source
      canonical
      semanticDomainType := presentation.domainType
      semanticValueType := sourceType.getAppArgs[1]!
      presentation
      accumulatedCertificate
      normalization
    }
    let sourceTerm ← exactExpressionSyntax source
    pure (sourceName, sourceTerm, sourceView, problemTypes, typed, sectionFVars,
      usedSourceParameterNames)
  let initialCertificateSyntax ← liftMacroM <|
    certificateReflTerm runner sourceTerm
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
    instantiatedSource
    usedSourceParameterNames
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
      | `(reformulationStep| conic) =>
          prepareTerminalConic state step
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
  if let some artifact := state.terminalConic? then
    outputRequests := outputRequests ++ #[
      { name := targetDeclName ++ `conicForm, ref := artifact.ref },
      { name := targetDeclName ++ `isConic, ref := artifact.ref }]
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

    let appliedTargetSyntax : CommandElabM (TSyntax `term) :=
      runTermElabM fun sectionFVars => do
        let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
        exactExpressionSyntax (← recoverDeclarationApplication targetDeclName typed.canonical)
    let emitCertificate : CommandElabM Unit := do
      let appliedTarget ← appliedTargetSyntax
      let normalizationLemmas ← liftMacroM <|
        normalizationSimpLemmas sourceName state.normalizationLemmas
      let targetSimp ← liftMacroM `(
        Lean.Parser.Tactic.simpLemma| $targetDeclIdent:term)
      let normalizationLemmas := normalizationLemmas.push targetSimp
      let normalizationEquivalence ← liftMacroM `(
        PTran.pointwiseEquivalence $stableSemantic $appliedTarget
          (fun _ => by
            simp only [$[$normalizationLemmas],*] <;> rfl)
          (fun _ => by
            simp only [$[$normalizationLemmas],*] <;> rfl))
      let normalization ← liftMacroM <|
        liftCertificateEquivalence state.runner normalizationEquivalence
      let equivalenceProof ← liftMacroM <|
        certificateTransTerm state.runner stableEquivalenceProof normalization
      let relation ← liftMacroM <|
        certificateRelationTerm state.runner sourceTerm appliedTarget
      let certificateCommand ← liftMacroM `(command|
        noncomputable def $certificateDeclIdent :
            $relation := by
          exact $equivalenceProof)
      elabCommand certificateCommand
    let emitAlias : CommandElabM Unit := do
      if let some aliasDeclIdent := aliasDeclIdent? then
        let (relation, certificateProof) ← runTermElabM fun sectionFVars => do
          let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
          let target ← recoverDeclarationApplication targetDeclName typed.canonical
          let source ← elabTerm sourceTerm none
          let relation ← state.runner.relationType source target
          let certificateProof ← recoverDeclarationApplication certificateDeclName relation true
          pure (← exactExpressionSyntax relation, ← exactExpressionSyntax certificateProof)
        let aliasCommand ← liftMacroM `(command|
          noncomputable abbrev $aliasDeclIdent : $relation := $certificateProof)
        elabCommand aliasCommand

    let elabCanonicalDeclarations : CommandElabM Unit := do
      if state.terminalConic?.isSome || state.instantiatedSource then
        emitCheckedTarget targetDeclIdent state
      else
        elabSemanticTarget targetDeclIdent sourceName state.checkpoint.semantic state.checkpoint.view
          state.removedConstraintNames stableSemantic state.simplifyExpLogTerms
      unless (← get).messages.hasErrors do
        emitCertificate
        unless (← get).messages.hasErrors do
          emitAlias

    let emitted ← if state.hasSubstitution || state.terminalConic?.isSome ||
        state.instantiatedSource then do
        elabCanonicalDeclarations
        pure !(← get).messages.hasErrors
      else
        match ← tryRawDeclarations targetCommand emitCertificate emitAlias with
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
      if let some artifact := state.terminalConic? then
        unless (← get).messages.hasErrors do
          emitTerminalArtifacts targetDeclName state artifact
      unless (← get).messages.hasErrors do
        refreshProblemView targetDeclName state.view state.instantiatedSource

/-- Elaborate a reformulation declaration and emit the transformed problem and
its composed global-equivalence certificate.  Planning, typed step validation,
declaration emission, companions, and metadata registration share one rollback
boundary. -/
@[command_elab reformulationCmd, command_elab appliedReformulationCmd]
def elabReformulation : CommandElab := fun stx =>
  withDeclarationTransaction (elabReformulationCore stx)

end PTran
