import PTran.Reformulation.Presentation
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

private partial def replaceIdent (stx : Lean.Syntax) (oldName : Name)
    (replacement : Lean.Syntax) : Lean.Syntax :=
  if stx.isIdent && stx.getId == oldName then
    replacement
  else
    stx.setArgs (stx.getArgs.map fun child => replaceIdent child oldName replacement)

/-- Give every occurrence of a newly introduced decision variable the same
fresh hygiene scope.  This keeps it distinct from an existing nested binder
with the same source spelling when the replacement is inserted into stored
presentation syntax. -/
private partial def scopeIdent (stx : Lean.Syntax) (name scopedName : Name) : Lean.Syntax :=
  if stx.isIdent && sameUserName stx.getId name then
    mkIdentFrom stx scopedName
  else
    stx.setArgs (stx.getArgs.map fun child => scopeIdent child name scopedName)

private def resolvedDeclName? : Lean.Syntax → Option Name
  | .ident _ _ _ preResolved => preResolved.findSome? fun
      | .decl name _ => some name
      | _ => none
  | _ => none

private def resolvedAppArgument? (stx : Lean.Syntax) (declaration : Name) :
    Option (TSyntax `term) := do
  let `(term| $function:ident $argument:term) := stx | none
  guard <| resolvedDeclName? function.raw == some declaration
  pure argument

private partial def simplifyExpLog (stx : Lean.Syntax) : MacroM Lean.Syntax := do
  let args ← stx.getArgs.mapM simplifyExpLog
  let simplified := stx.setArgs args
  if let some logArgument := resolvedAppArgument? simplified ``Real.log then
    if let some argument := resolvedAppArgument? logArgument.raw ``Real.exp then
      simplifyExpLog argument.raw
    else
      pure simplified
  else
    match simplified with
    | `(term| 0 < $positive:term) =>
        if (resolvedAppArgument? positive.raw ``Real.exp).isSome then
          `(True)
        else
          pure simplified
    | `(term| ($inner:term)) =>
        if inner.raw.isIdent then pure inner.raw else pure simplified
    | _ => pure simplified

private def isTrueSyntax (stx : Lean.Syntax) : Bool :=
  match stx with
  | `(True) => true
  | _ => false

private def mkProduct (terms : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  if h : terms.size > 0 then
    let mut result := terms[0]
    for i in [1:terms.size] do
      result ← `(⟨$result, $(terms[i]!)⟩)
    pure result
  else
    Macro.throwError "a reformulated problem must have at least one decision variable"

private def mkProductPattern (names : Array Name) : MacroM (TSyntax `term) := do
  let terms := names.map fun name => (⟨mkIdent name⟩ : TSyntax `term)
  mkProduct terms

private def mkConjunctionEvidence (proof : TSyntax `term) (index count : Nat) :
    MacroM (TSyntax `term) := do
  let mut evidence := proof
  for _ in [:index] do
    evidence ← `(($evidence).2)
  if index + 1 < count then
    evidence ← `(($evidence).1)
  pure evidence

private partial def mkProductProjection (point : TSyntax `term)
    (index count : Nat) : MacroM (TSyntax `term) := do
  if count == 0 || index >= count then
    Macro.throwError "invalid product projection"
  else if count == 1 then
    pure point
  else if index + 1 == count then
    `(($point).2)
  else
    let initial ← `(($point).1)
    mkProductProjection initial index (count - 1)

private partial def collectIdents (stx : Lean.Syntax) (result : NameSet := {}) : NameSet :=
  match stx with
  | .ident _ _ value preResolved =>
      if preResolved.any fun
          | .decl _ _ => true
          | _ => false then
        result
      else
        -- Candidate locals must retain the scopes used by the replacement.
        result.insert value
  | _ => stx.getArgs.foldl (fun result child => collectIdents child result) result

private def newBinderCandidates (view : PTran.Syntax.ProblemView) (oldName : Name)
    (replacement : Lean.Syntax) : CommandElabM (Array Name) := do
  let localNames : NameSet := view.binders.foldl
    (fun names binder => names.insert binder.name.eraseMacroScopes) ({} : NameSet)
  let env ← getEnv
  let candidates := (collectIdents replacement).toList.filter fun name =>
    !name.isAnonymous && !sameUserName name oldName &&
      !localNames.contains name.eraseMacroScopes && !env.contains name
  pure candidates.toArray

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
  | retryWithSemanticTarget

private inductive RawDeclarationStage where
  | target
  | certificate
  | alias
  deriving BEq

/-- Try the source-aligned target first.  A certificate failure means that
re-elaborating presentation syntax selected different implicit data (for
example, a newly scoped instance or coercion), so the entire attempt is rolled
back and the caller may declare the stabilized semantic term instead.
Target and alias failures retain their diagnostics and are never masked. -/
private def tryRawDeclarations (targetCommand certificateCommand : Syntax)
    (aliasCommand? : Option Syntax) : CommandElabM RawDeclarationResult := do
  let savedState ← get
  set { savedState with messages := .empty }
  let mut stage := RawDeclarationStage.target
  try
    elabCommand targetCommand
    if (← get).messages.hasErrors then
      let resultingState ← get
      set { resultingState with
        messages := savedState.messages ++ resultingState.messages }
      return .failed

    stage := .certificate
    elabCommand certificateCommand
    if (← get).messages.hasErrors then
      set savedState
      return .retryWithSemanticTarget

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
        if stage == .certificate then do
          set savedState
          pure .retryWithSemanticTarget
        else do
          set { savedState with
            messages := savedState.messages ++ resultingState.messages }
          throw exception
    | .internal _ _ =>
        set savedState
        throw exception

private abbrev SurfaceMaterializerM :=
  StateT (Option SurfaceMaterialization) CommandElabM

private def findBinderIndex (view : PTran.Syntax.ProblemView) (name : Name) : Option Nat :=
  view.binders.findIdx? fun binder => sameUserName binder.name name

private def inferNewBinder (state : ReformState) (oldName : Name)
    (binderIndex : Nat) (replacement : TSyntax `term) : CommandElabM Name := do
  let candidates ← newBinderCandidates state.view oldName replacement.raw
  if candidates.isEmpty then
    throwErrorAt replacement
      "cannot determine the new decision variable; the substitution expression must contain one new identifier"
  let usedCandidates ← withTypedPresentation state fun presentation =>
    withPresentationBinders presentation fun binderTypes _ => do
      let candidateDeclarations := candidates.map fun name =>
        (name, binderTypes[binderIndex]!)
      withLocalDeclsDND candidateDeclarations fun candidateFVars => do
        let expression ← elabTerm replacement (some binderTypes[binderIndex]!)
        synthesizeSyntheticMVarsNoPostponing
        let expression ← instantiateMVars expression
        pure <| candidates.zip candidateFVars |>.filterMap fun (name, fvar) =>
          if expression.containsFVar fvar.fvarId! then some name else none
  if (← get).messages.hasErrors then
    throwAbortCommand
  match usedCandidates.toList with
  | [name] => pure name
  | [] =>
      throwErrorAt replacement
        "cannot determine the new decision variable; the substitution expression must contain one new identifier"
  | names =>
      throwErrorAt replacement
        "ambiguous substitution: expected exactly one new decision variable, found {names}"

private def replacementIsRealExpOf (state : ReformState)
    (binderIndex : Nat) (newName : Name) (replacement : TSyntax `term) :
    CommandElabM Bool :=
  withTypedPresentation state fun presentation => do
    let oldBinder := presentation.binders[binderIndex]!
    let presentation := { presentation with
      binders := presentation.binders.set! binderIndex { oldBinder with name := newName }
    }
    withPresentationBinders presentation fun binderTypes binders => do
      let expression ← elabTerm replacement (some binderTypes[binderIndex]!)
      synthesizeSyntheticMVarsNoPostponing
      let expression ← instantiateMVars expression
      let arguments := expression.getAppArgs
      pure <| expression.getAppFn.isConstOf ``Real.exp && arguments.size == 1 &&
        arguments[0]!.fvarId? == binders[binderIndex]!.fvarId?

private structure PositiveConstraintMatch where
  index : Nat
  normalization? : Option (TSyntax `term)

private def findPositiveConstraint (state : ReformState)
    (binderIndex : Nat) : CommandElabM (Option PositiveConstraintMatch) :=
  withTypedPresentation state fun presentation =>
  withPresentationBinders presentation fun _ binders => do
    let point ← packPoint binders
    let binder : TSyntax `term := ⟨mkIdent presentation.binders[binderIndex]!.name⟩
    let expectedSyntax ← liftMacroM `(0 < $binder)
    let expected ← elabTerm expectedSyntax (some (mkSort Level.zero))
    synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    for index in [:presentation.constraints.size] do
      let candidate ← simpOnly <| mkApp presentation.constraints[index]!.predicate point
      if ← isDefEq candidate expected then
        let normalization? ← if candidate == expected then pure none else do
          -- Preserve the full definitional equivalence, including nested aliases,
          -- as a checked rewrite instead of remembering only a head declaration.
          let equivalence := mkApp2 (mkConst ``Iff) candidate expected
          let proof := mkExpectedPropHint (mkApp (mkConst ``Iff.rfl) expected) equivalence
          -- Close over section parameters too, including anonymous instances.
          let proof ← mkLambdaFVars (← getLCtx).getFVars proof (usedOnly := true)
          check proof
          pure <| some (← exactExpressionSyntax proof)
        return some { index, normalization? }
    pure none

private def constraintIsTypedTrue (state : ReformState)
    (index : Nat) : CommandElabM Bool :=
  withTypedPresentation state fun presentation =>
    withLocalDeclD `point presentation.domainType fun point =>
      isDefEq (mkApp presentation.constraints[index]!.predicate point) (mkConst ``True)

private def materializeSubstitution (state : ReformState) (step : Lean.Syntax)
    (replacement : TSyntax `term)
    (providedCertificate? : Option (TSyntax `term))
    (oldName : Name) (binderIndex : Nat)
    (allocation : PTran.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some newName := allocation.findName? 0
    | throwErrorAt replacement "internal error: missing substitution binder allocation"
  let scopedNewName ← withFreshMacroScope do
    MonadQuotation.addMacroScope newName
  let replacement : TSyntax `term :=
    ⟨scopeIdent replacement.raw newName scopedNewName⟩

  let oldBinder := state.view.binders[binderIndex]!
  let newBinders := state.view.binders.set! binderIndex {
    oldBinder with name := scopedNewName
  }
  let isRegisteredExp ← replacementIsRealExpOf state binderIndex scopedNewName replacement
  if (← get).messages.hasErrors then
    throwAbortCommand
  let positiveMatch? ← if isRegisteredExp then
      findPositiveConstraint state binderIndex
    else
      pure none
  let positiveIndex? := positiveMatch?.map (·.index)
  let normalizationLemmas := match positiveMatch?.bind (·.normalization?) with
    | some proof => state.normalizationLemmas.push proof
    | none => state.normalizationLemmas

  let binderNames := newBinders.map fun binder => binder.name
  let domainType := state.semanticDomainType
  let domainPattern ← liftMacroM <| mkProductPattern binderNames
  let mapComponents : Array (TSyntax `term) := state.view.binders.mapIdx fun i binder =>
    if i == binderIndex then replacement else ⟨mkIdent binder.name⟩
  let mapResult ← liftMacroM <| mkProduct mapComponents
  let mapTerm ← liftMacroM `(fun ($domainPattern : $domainType) => $mapResult)

  let objective ← liftMacroM <|
    simplifyExpLog (replaceIdent state.view.objective oldBinder.name replacement)
  let mut constraints : Array PTran.Syntax.ConstraintView := #[]
  let mut removedConstraintNames := state.removedConstraintNames
  for index in [:state.view.constraints.size] do
    let constraint := state.view.constraints[index]!
    let wasPresentedAsTrue ← constraintIsTypedTrue state index
    let proposition ← liftMacroM <|
      simplifyExpLog (replaceIdent constraint.proposition oldBinder.name replacement)
    let provedTrue := isTrueSyntax proposition || positiveIndex? == some index
    if provedTrue && !wasPresentedAsTrue then
      removedConstraintNames :=
        removedConstraintNames.insert constraint.name.eraseMacroScopes
    else
      constraints := constraints.push { constraint with proposition }
  let newView : PTran.Syntax.ProblemView := {
    state.view with
    binders := newBinders
    objective
    constraints
  }

  let stepCertificate ← match providedCertificate? with
    | some proofTerm =>
        pure ⟨← liftTermElabM <| PTran.Syntax.preResolveTerm proofTerm.raw⟩
    | none => do
        unless isRegisteredExp do
          throwErrorAt replacement
            "no registered substitution rule matches this expression; provide `using` with a `FeasibleSurjection` certificate"
        let some positiveIndex := positiveIndex?
          | throwErrorAt step
              "the registered exponential rule requires the current constraint `0 < {oldName.eraseMacroScopes}`; provide `using` for a more general feasible domain"
        let current := state.semantic
        -- Earlier steps may have removed positivity constraints through aliases.
        let normalizationLemmas ← liftMacroM <|
          normalizationSimpLemmas state.source state.normalizationLemmas
        let pointIdent : TSyntax `ident := ⟨mkIdent `point⟩
        let pointTerm : TSyntax `term := ⟨pointIdent.raw⟩
        let sourcePoint ← liftMacroM `(($pointTerm).1)
        let selectedSource ← liftMacroM <|
          mkProductProjection sourcePoint binderIndex state.view.binders.size
        let mut preimageComponents : Array (TSyntax `term) := #[]
        for index in [:state.view.binders.size] do
          let component ← liftMacroM <|
            mkProductProjection sourcePoint index state.view.binders.size
          if index == binderIndex then
            preimageComponents := preimageComponents.push (← liftMacroM `(Real.log $component))
          else
            preimageComponents := preimageComponents.push component
        let preimage ← liftMacroM <| mkProduct preimageComponents
        let canonicalFeasible ← withTypedPresentation state fun presentation => do
          let feasible ← mkFeasibleFunction presentation.domainType
            (presentation.constraints.map (·.predicate))
          -- Anonymous section instances get fresh names on each elaboration.
          -- Abstract them so the certificate can infer them in its own context.
          let instances ← (← getLCtx).getFVars.filterM fun fvar =>
            return (← fvar.fvarId!.getDecl).binderInfo.isInstImplicit
          let feasible ← mkLambdaFVars instances (← simpOnly feasible) (usedOnly := true)
          exactExpressionSyntax feasible
        let feasibleIdent : TSyntax `ident := ⟨mkIdent `normalizedFeasible⟩
        let feasible : TSyntax `term := ⟨feasibleIdent.raw⟩
        let positiveEvidence ← liftMacroM <|
          mkConjunctionEvidence feasible positiveIndex state.view.constraints.size
        liftMacroM `(
          ({
            preimage := fun $pointIdent => $preimage
            rightInverse := fun $pointIdent => by
              have $feasibleIdent : ($canonicalFeasible) ($pointTerm).1 := by
                simpa only [$[$normalizationLemmas],*] using ($pointTerm).2
              have positive : 0 < $selectedSource := by
                exact $positiveEvidence
              simp only [Real.exp_log positive]
          } : PTran.FeasibleSurjection $current $mapTerm))

  let current := state.semantic
  let nextSemantic ← liftMacroM `(PTran.Problem.pullback $current $mapTerm)
  let primitiveEquivalence ← liftMacroM `(
    PTran.pullbackEquivalence $current $mapTerm $stepCertificate)
  let primitive ← liftMacroM <|
    liftCertificateEquivalence state.runner primitiveEquivalence
  pure {
    view := newView
    semantic := nextSemantic
    semanticDomainType := state.semanticDomainType
    primitiveCertificate := primitive
    simplifyExpLogTerms := true
    hasSubstitution := true
    removedConstraintNames
    normalizationLemmas
  }

private def prepareSubstitution (state : ReformState) (step : Lean.Syntax)
    (oldIdent : TSyntax `ident) (replacement : TSyntax `term)
    (providedCertificate? : Option (TSyntax `term)) :
    CommandElabM SurfaceStepDraft := do
  let replacement : TSyntax `term :=
    ⟨← liftTermElabM <| PTran.Syntax.preResolveTerm replacement.raw⟩
  let oldName := oldIdent.getId
  let some binderIndex := findBinderIndex state.view oldName
    | throwErrorAt oldIdent "unknown decision variable `{oldName.eraseMacroScopes}`"
  let newName ← inferNewBinder state oldName binderIndex replacement
  let request : PTran.Elab.Reformulation.NameRequest := {
    id := 0
    kind := .inferredDecisionBinder
    requested := newName
    ref := replacement.raw
  }
  pure {
    nameRequests := #[request]
    materialize := fun allocation =>
      materializeSubstitution state step replacement providedCertificate?
        oldName binderIndex allocation
  }

private def materializeObjectiveBound (state : ReformState)
    (binder : TSyntax `ident)
    (expectedSense : PTran.Syntax.ObjectiveSense)
    (allocation : PTran.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some binderName := allocation.findName? 0
    | throwErrorAt binder "internal error: missing objective-bound binder allocation"
  let some constraintName := allocation.findName? 1
    | throwErrorAt binder "internal error: missing objective-bound label allocation"
  let scopedBinderName ← withFreshMacroScope do
    MonadQuotation.addMacroScope binderName

  let valueType : TSyntax `term := ⟨state.presentationValueType⟩
  let newBinder : PTran.Syntax.BinderView := {
    name := scopedBinderName
    typeSyntax := valueType
  }
  let boundName := mkIdent scopedBinderName
  let oldObjective : TSyntax `term := ⟨state.view.objective⟩
  let proposition ← liftMacroM <| match expectedSense with
    | .minimize => `($oldObjective ≤ $boundName)
    | .maximize => `($boundName ≤ $oldObjective)
  let constraint : PTran.Syntax.ConstraintView := {
    name := constraintName
    proposition
  }
  let newView : PTran.Syntax.ProblemView := {
    state.view with
    binders := state.view.binders.push newBinder
    objective := boundName
    constraints := state.view.constraints.push constraint
  }

  let current := state.semantic
  let nextSemantic ← liftMacroM <| match expectedSense with
    | .minimize => `(PTran.Problem.epigraph $current)
    | .maximize => `(PTran.Problem.hypograph $current)
  let primitiveEquivalence ← liftMacroM <| match expectedSense with
    | .minimize => `(PTran.epigraphEquivalence $current)
    | .maximize => `(PTran.hypographEquivalence $current)
  let primitive ← liftMacroM <|
    liftCertificateEquivalence state.runner primitiveEquivalence
  let currentDomainType := state.semanticDomainType
  let valueType := state.semanticValueType
  let nextDomainType ← liftMacroM `($currentDomainType × $valueType)
  pure {
    view := newView
    semantic := nextSemantic
    semanticDomainType := nextDomainType
    primitiveCertificate := primitive
    simplifyExpLogTerms := state.simplifyExpLogTerms
    hasSubstitution := state.hasSubstitution
    removedConstraintNames := state.removedConstraintNames
    normalizationLemmas := state.normalizationLemmas
  }

private def prepareObjectiveBound (state : ReformState) (step : Lean.Syntax)
    (binder : TSyntax `ident) (explicitLabel? : Option (TSyntax `ident))
    (expectedSense : PTran.Syntax.ObjectiveSense) :
    CommandElabM SurfaceStepDraft := do
  unless state.view.sense == expectedSense do
    let expected := match expectedSense with
      | .minimize => "epigraph"
      | .maximize => "hypograph"
    let actual := match state.view.sense with
      | .minimize => "minimization"
      | .maximize => "maximization"
    throwErrorAt step "`{expected}` is not valid for a {actual} problem"
  let binderName := binder.getId
  let generatedName := Name.mkSimple <| match expectedSense with
    | .minimize => s!"epigraph_{binderName.eraseMacroScopes}"
    | .maximize => s!"hypograph_{binderName.eraseMacroScopes}"
  let constraintName := match explicitLabel? with
    | some label => label.getId.eraseMacroScopes
    | none => generatedName
  let binderRequest : PTran.Elab.Reformulation.NameRequest := {
    id := 0
    kind := .explicitDecisionBinder
    requested := binderName
    ref := binder.raw
  }
  let constraintRequest : PTran.Elab.Reformulation.NameRequest := {
    id := 1
    kind := if explicitLabel?.isSome then
      .explicitConstraintLabel
    else
      .fixedPublicDefault
    requested := constraintName
    ref := explicitLabel?.map (·.raw) |>.getD binder.raw
  }
  pure {
    nameRequests := #[binderRequest, constraintRequest]
    materialize := fun allocation =>
      materializeObjectiveBound state binder expectedSense allocation
  }

private def validateTypedPrimitive (state : ReformState)
    (result : SurfaceStepResult) :
    CommandElabM (PTran.Elab.Reformulation.StepResult × Array Expr) :=
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
    let env ← getEnv
    let some sourceView := PTran.Syntax.getProblemView? env state.sourceName
      | throwError "source presentation metadata disappeared during reformulation"
    let nextCanonical ← canonicalTargetExpression state.sourceName state.source
      sourceView result.removedConstraintNames result.semantic
      result.simplifyExpLogTerms
    let currentPresentation := typed.presentation
    let nextPresentation ←
      typedPresentationFromExpression nextCanonical result.view
    let normalization ←
      checkedPointwiseNormalization state.source next nextCanonical
        result.normalizationLemmas
    let presentationDelta ← presentationDeltaBetween currentPresentation
      nextPresentation normalization.objectiveEquality normalization.feasibleIff
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
    pure (typedResult, sectionFVars)

private def typedStepPlan (state : ReformState) (draft : SurfaceStepDraft) :
    PTran.Elab.Reformulation.StepPlan SurfaceMaterializerM := {
  nameRequests := draft.nameRequests
  materialize := fun allocation _ => do
    let surface ← draft.materialize allocation
    let (result, sectionFVars) ←
      validateTypedPrimitive state surface
    pure (result, some { surface, sectionFVars })
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

private def runTypedStepPlan (state : ReformState) (draft : SurfaceStepDraft) :
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

private def commitSurfaceStep (state : ReformState)
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
    certificateSyntax
    simplifyExpLogTerms := surface.simplifyExpLogTerms
    hasSubstitution := surface.hasSubstitution
    removedConstraintNames := surface.removedConstraintNames
    normalizationLemmas := surface.normalizationLemmas
  }

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
      elabSemanticTarget targetDeclIdent sourceName sourceTerm sourceView
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
        | .retryWithSemanticTarget =>
            elabCanonicalDeclarations
            pure !(← get).messages.hasErrors
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
