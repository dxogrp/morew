/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Reformulation.Step
import Lean.Elab.MutualDef

/-! Declare a transformed problem and its GlobalEquivalence certificate.
Terminal conic and nlp steps also emit structural forms and representability proofs. -/

namespace Morew

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser
open Morew.Elab.Reformulation

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

/-- Emit an elaborated definition with section arguments collected before proof extraction. -/
private def emitDefinitionWithParameters (target : TSyntax `ident)
    (sectionVars : Array Expr) (scope : Command.Scope) (type value : Expr) :
    TermElabM Expr := do
  synthesizeSyntheticMVarsNoPostponing
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then
    throwErrorAt target "emitted definition contains unresolved metavariables"
  let used := Lean.collectFVars (Lean.collectFVars {} type) value
  let (_, _, parameters) ← removeUnused sectionVars used
  let definition ← `(Parser.Command.definition|
    def $target : $(← Term.exprToSyntax type) := $(← Term.exprToSyntax value))
  Term.elabMutualDef sectionVars scope #[
    Command.mkDefViewOfDef { computeKind := .noncomputable } definition]
  let name := target.getId.replacePrefix `_root_ Name.anonymous
  -- Retain checked universe names and section parameters during generalization.
  let info ← getConstInfo name
  let mut application := Lean.mkConst name (info.levelParams.map Level.param)
  let mut applicationType ← inferType application
  for parameter in parameters do
    let .forallE _ domain body _ ← whnf applicationType
      | throwErrorAt target "emitted definition has unexpected parameters"
    unless ← isDefEq domain (← inferType parameter) do
      throwErrorAt target "emitted definition has unexpected parameter types"
    application := mkApp application parameter
    applicationType := body.instantiate1 parameter
  unless ← isDefEq (← inferType application) type do
    throwErrorAt target "emitted definition has unexpected parameter types"
  unless ← isDefEq application value do
    throwErrorAt target "emitted definition does not match its checked expression"
  application ← instantiateMVars application
  if application.hasMVar then
    throwErrorAt target "emitted definition contains unresolved universe parameters"
  pure application

/-- Freeze the retained application before leaving its section-variable context. -/
private def emitDefinition (target : TSyntax `ident)
    (elaborate : Array Expr → TermElabM (Expr × Expr)) :
    CommandElabM (TSyntax `term) := do
  let scope ← getScope
  -- Lean's quotation-context wrapper returns Unit.
  let result ← IO.mkRef (none : Option (TSyntax `term))
  withExporting (isExporting := scope.isPublic) do
  withInitQuotContext (some (hash #[target.getId])) do
    let application ← runTermElabM fun sectionVars => do
      let (type, value) ← elaborate sectionVars
      exactExpressionSyntax (← emitDefinitionWithParameters target sectionVars scope type value)
    result.set (some application)
  let some application ← result.get
    | throwErrorAt target "internal error: emitted definition application was not retained"
  pure application

private inductive RawDeclarationResult where
  | success (target : TSyntax `term)
  | failed
  | retryWithSemanticTarget (messages : MessageLog)

private inductive RawDeclarationStage where
  | target
  | certificate
  | alias
  deriving BEq

/-- Emit declarations using source syntax, retrying target and certificate failures with
explicit semantic types and normalization. Preserve the original error if retry fails;
alias failures and internal exceptions propagate. -/
private def tryRawDeclarations (emitTarget : CommandElabM (TSyntax `term))
    (emitCertificate : TSyntax `term → CommandElabM (TSyntax `term))
    (emitAlias : TSyntax `term → CommandElabM Unit) : CommandElabM RawDeclarationResult := do
  let savedState ← get
  set { savedState with messages := .empty }
  let mut stage := RawDeclarationStage.target
  try
    let target ← emitTarget
    if (← get).messages.hasErrors then
      let messages := (← get).messages
      set savedState
      return .retryWithSemanticTarget messages

    stage := .certificate
    let appliedCertificate ← emitCertificate target
    if (← get).messages.hasErrors then
      let messages := (← get).messages
      set savedState
      return .retryWithSemanticTarget messages

    stage := .alias
    emitAlias appliedCertificate
    if (← get).messages.hasErrors then
      let resultingState ← get
      set { resultingState with
        messages := savedState.messages ++ resultingState.messages }
      return .failed

    let resultingState ← get
    set { resultingState with
      messages := savedState.messages ++ resultingState.messages }
    pure (.success target)
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
    (request : Morew.Elab.Reformulation.CompanionRequest)
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

-- Preserve occurrence structure and OrderDual after checking canonical agreement.
private def emitCheckedTarget (target : TSyntax `ident) (state : ReformState) :
    CommandElabM (TSyntax `term) :=
  emitDefinition target fun sectionVars => do
    let typed := state.typed.replaceFVars state.sectionFVars sectionVars
    let type ← mkAppM ``Morew.Problem
      #[typed.presentation.domainType, typed.semanticValueType]
    -- Retain definitions and occurrences in the emitted declaration value.
    let term ← liftMacroM state.view.toTermSyntax
    let carrier ← elabTerm term (some type)
    synthesizeSyntheticMVarsNoPostponing
    let carrier ← instantiateMVars carrier
    unless ← isDefEq carrier typed.canonical do
      -- Prove canonical agreement while retaining dependent definition types.
      discard <| checkedPointwiseNormalization state.sourceName carrier
        typed.canonical state.normalizationLemmas
    pure (type, carrier)

private theorem problemEquality {X : Type u} {V : Type v} (p q : Morew.Problem X V)
    (objective : ∀ x, p.objective x = q.objective x)
    (feasible : ∀ x, p.feasible x ↔ q.feasible x) : p = q := by
  cases p with
  | mk po pf =>
    cases q with
    | mk qo qf =>
      exact congrArg₂ Morew.Problem.mk (funext objective)
        (funext fun x => propext (feasible x))

private def emitTerminalArtifacts (targetName : Name) (state : ReformState)
    (appliedTarget : TSyntax `term) (artifact : CheckedTerminalArtifact) :
    CommandElabM Unit := do
  let scope ← getScope
  withExporting (isExporting := scope.isPublic) do
  withInitQuotContext (some (hash #[targetName])) do
    runTermElabM fun sectionVars => do
      let artifact := artifact.replaceFVars state.sectionFVars sectionVars
      let target ← elabTerm appliedTarget none
      let typed := state.typed.replaceFVars state.sectionFVars sectionVars
      let represented := artifact.representedProblem
      let equality ← if ← isDefEq represented target then
          mkEqRefl represented
        else do
          -- Use proved normalization for retained dependent definitions.
          let some targetBody ← unfoldDefinition? target
            | throwErrorAt artifact.ref
                "cannot inspect the emitted {artifact.adapter.description} target"
          let normalization ← checkedPointwiseNormalization state.sourceName
            represented targetBody state.normalizationLemmas
          mkAppM ``problemEquality #[represented, target,
            normalization.objectiveEquality, normalization.feasibleIff]
      let form ← artifact.adapter.retarget artifact.form target equality
      discard <| withRef artifact.ref <|
        artifact.adapter.validate form target typed.presentation.sense
      synthesizeSyntheticMVarsNoPostponing
      let form ← instantiateMVars form
      let formType ← instantiateMVars (← inferType form)
      if form.hasMVar || formType.hasMVar then
        throwErrorAt artifact.ref
          "emitted {artifact.adapter.description} form contains unresolved metavariables"
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        checkWithKernel form
      let formIdent := rootIdentFrom artifact.ref (targetName ++ artifact.adapter.formSuffix)
      let propertyIdent := rootIdentFrom artifact.ref (targetName ++ artifact.adapter.propertySuffix)
      let namedForm ← emitDefinitionWithParameters formIdent sectionVars scope formType form
      -- Use the emitted form's stored instances when constructing its property.
      let property ← artifact.adapter.property namedForm
      synthesizeSyntheticMVarsNoPostponing
      let property ← instantiateMVars property
      if property.hasMVar then
        throwErrorAt artifact.ref
          "emitted {artifact.adapter.description} property contains unresolved metavariables"
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        checkWithKernel property
      let propertyType ← inferType property
      let propertyDefinition ← `(Parser.Command.theorem|
        theorem $propertyIdent : $(← exactExpressionSyntax propertyType) :=
          $(← exactExpressionSyntax property))
      -- Retain the certificate's dependency closure and omit unused instances.
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
    let some template := Morew.Syntax.getProblemView? (← getEnv) sourceName
      | throwError "declaration `{sourceName}` has no registered problem presentation"
    let problemTypes ← problemTypeSyntaxFromExpression source
    let sourceType ← whnf (← inferType source)
    let mut usedSourceParameterNames := #[]
    if instantiatedSource then
      let dependencies ← (Lean.collectFVars {} source).addDependencies
      for id in dependencies.fvarSet.toArray do
        let name := (← id.getDecl).userName.eraseMacroScopes
        if template.binders.any (sameVisibleName ·.name name) then
          throwError "source parameter `{name}` conflicts with a decision variable; rename the outer parameter"
        if template.definitions.any (sameVisibleName ·.name name) then
          throwError "source parameter `{name}` conflicts with a model-local definition; rename the outer parameter"
        unless usedSourceParameterNames.contains name do
          usedSourceParameterNames := usedSourceParameterNames.push name
    let canonical ← canonicalTargetExpressionFromExpressions sourceName source source
      template {} source false
    let sourceView ← problemViewFromExpression source template (instantiateBinderTypes := true)
    let presentation ← typedPresentationFromExpression canonical sourceView
    let normalization ← checkedPointwiseNormalization sourceName source canonical #[]
    let accumulatedCertificate ← runner.reflexivity source
    synthesizeSyntheticMVarsNoPostponing
    let accumulatedCertificate ← instantiateMVars accumulatedCertificate
    let typed : Morew.Elab.Reformulation.RunnerState := {
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
    certificateSyntax := initialCertificateSyntax
    source := sourceTerm
    sourceName
    instantiatedSource
    usedSourceParameterNames
    checkpoint := {
      semantic := sourceTerm, semanticAnchor := sourceTerm, view := sourceView }
    liveCheckpointRows := Array.range sourceView.constraints.size
    runner
  }

  for step in steps do
    if state.typed.status == .terminal then
      throwErrorAt step "cannot apply a reformulation step after a terminal step"
    let draft ← prepareStep state step
    let (result, materialization) ← runTypedStepPlan state draft
    state ← commitSurfaceStep state result materialization

  let mut outputRequests :
      Array Morew.Elab.Reformulation.DeclarationNameRequest := #[
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
  if let some artifact := state.terminalArtifact? then
    outputRequests := outputRequests ++ #[
      { name := targetDeclName ++ artifact.adapter.formSuffix, ref := artifact.ref },
      { name := targetDeclName ++ artifact.adapter.propertySuffix, ref := artifact.ref }]
  match Morew.Elab.Reformulation.preflightDeclarationNames
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
    let emitRawTarget := emitDefinition targetDeclIdent fun _ => do
      let value ← elabTerm targetTerm none
      pure (← inferType value, value)

    let emitCertificate (appliedTarget : TSyntax `term) :
        CommandElabM (TSyntax `term) := do
      let normalizationLemmas ← liftMacroM <|
        normalizationSimpLemmas sourceName state.normalizationLemmas
      let targetSimp ← liftMacroM `(
        Lean.Parser.Tactic.simpLemma| $targetDeclIdent:term)
      let normalizationLemmas := normalizationLemmas.push targetSimp
      let normalizationEquivalence ← liftMacroM `(
        Morew.pointwiseEquivalence $stableSemantic $appliedTarget
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
      emitDefinition certificateDeclIdent fun _ => do
        let type ← elabTerm relation none
        let value ← elabTermEnsuringType equivalenceProof type
        pure (type, value)
    let emitAlias (appliedCertificate : TSyntax `term) : CommandElabM Unit := do
      if let some aliasDeclIdent := aliasDeclIdent? then
        let relation ← runTermElabM fun _ => do
          let proof ← elabTerm appliedCertificate none
          exactExpressionSyntax (← inferType proof)
        let aliasCommand ← liftMacroM `(command|
          noncomputable abbrev $aliasDeclIdent : $relation := $appliedCertificate)
        elabCommand aliasCommand

    let elabCanonicalDeclarations : CommandElabM (Option (TSyntax `term)) := do
      let target ← emitCheckedTarget targetDeclIdent state
      if (← get).messages.hasErrors then return none
      let appliedCertificate ← emitCertificate target
      if (← get).messages.hasErrors then return none
      emitAlias appliedCertificate
      pure <| if (← get).messages.hasErrors then none else some target

    let appliedTarget? ← if state.hasSubstitution || state.terminalArtifact?.isSome ||
        state.instantiatedSource then do
        elabCanonicalDeclarations
      else
        match ← tryRawDeclarations emitRawTarget emitCertificate emitAlias with
        | .success target => pure (some target)
        | .failed => pure none
        | .retryWithSemanticTarget rawMessages =>
            try
              let target? ← elabCanonicalDeclarations
              if target?.isNone then
                modify fun state => { state with messages := state.messages ++ rawMessages }
              pure target?
            catch exception =>
              modify fun state => { state with messages := state.messages ++ rawMessages }
              throw exception
    if let some appliedTarget := appliedTarget? then
      for companion in state.typed.companions do
        unless (← get).messages.hasErrors do
          emitCompanionDeclaration companion state.sectionFVars
      if let some artifact := state.terminalArtifact? then
        unless (← get).messages.hasErrors do
          emitTerminalArtifacts targetDeclName state appliedTarget artifact
      unless (← get).messages.hasErrors do
        refreshProblemView targetDeclName state.view (instantiateBinderTypes := true)

/-- Elaborate steps and emit the target, equivalence, companions, and metadata in one transaction. -/
@[command_elab reformulationCmd, command_elab appliedReformulationCmd]
def elabReformulation : CommandElab := fun stx =>
  withDeclarationTransaction (elabReformulationCore stx)

end Morew
