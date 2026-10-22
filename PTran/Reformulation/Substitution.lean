import PTran.Elab.Atom
import PTran.Reformulation.Presentation

/-!
# Substitution steps

Inference, rule selection, and proof-producing substitution materialization.
-/

namespace PTran.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

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
      let some atom ← PTran.Elab.Atom.recognizeAtom? expression
        | pure false
      pure <| atom.kind == .exp && atom.operands.size == 1 &&
        atom.operands[0]!.fvarId? == binders[binderIndex]!.fvarId?

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
          normalizationSimpLemmas state.sourceName state.normalizationLemmas
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

/-- Plan a substitution and defer materialization until name preflight succeeds. -/
def prepareSubstitution (state : ReformState) (step : Lean.Syntax)
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

end PTran.Reformulation.Internal
