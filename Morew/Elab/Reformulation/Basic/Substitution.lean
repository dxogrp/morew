/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Atom
import Morew.Elab.Expr
import Morew.Elab.Substitution.Coordinates
import Morew.Elab.Substitution.Match
import Morew.Elab.Substitution.Rules
import Morew.Elab.Reformulation.View

/-! Infer, select, and construct certified coordinate substitutions. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

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

private def mkProduct (terms : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  if h : terms.size > 0 then
    let mut result := terms[0]
    for i in [1:terms.size] do
      result ← `(⟨$result, $(terms[i]!)⟩)
    pure result
  else
    Macro.throwError "a reformulated problem must have at least one optimization variable"

private def mkProductPattern (names : Array Name) : MacroM (TSyntax `term) := do
  let terms := names.map fun name => (⟨mkIdent name⟩ : TSyntax `term)
  mkProduct terms

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

/-- Resolve globals while retaining displayed bindings and captured global references. -/
private partial def preResolveReplacement (view : Morew.Syntax.ProblemView)
    (stx : Lean.Syntax) : TermElabM Lean.Syntax := do
  if stx.isIdent then
    let name := stx.getId.eraseMacroScopes
    if view.binders.any (fun binder => binder.name.eraseMacroScopes.isPrefixOf name) ||
        view.definitions.any (fun definition => definition.name.eraseMacroScopes.isPrefixOf name) then
      pure stx
    else
      Morew.Syntax.preResolveTerm stx
  else
    pure <| stx.setArgs (← stx.getArgs.mapM (preResolveReplacement view))

private def newBinderCandidates (view : Morew.Syntax.ProblemView) (oldName : Name)
    (replacement : Lean.Syntax) : CommandElabM (Array Name) := do
  let localNames : NameSet := view.binders.foldl
    (fun names binder => names.insert binder.name.eraseMacroScopes) ({} : NameSet)
  let localNames := view.definitions.foldl
    (fun names definition => names.insert definition.name.eraseMacroScopes) localNames
  let localNames := localNames.toList
  let ambientNames ← runTermElabM fun _ => do
    (← getLCtx).getFVars.mapM fun fvar => do
      return (← fvar.fvarId!.getDecl).userName.eraseMacroScopes
  let env ← getEnv
  let candidates := (collectIdents replacement).toList.filter fun name =>
    !name.isAnonymous && !sameVisibleName name oldName &&
      !(localNames.any fun localName => localName.isPrefixOf name.eraseMacroScopes) &&
      !env.contains name
  let fresh := candidates.filter fun name =>
    !(ambientNames.any fun localName =>
      !localName.isAnonymous && localName.isPrefixOf name.eraseMacroScopes)
  -- Prefer fresh names over ambient coefficients; otherwise apply shadowing and collision checks.
  pure (if fresh.isEmpty then candidates else fresh).toArray

private def findBinderIndex (view : Morew.Syntax.ProblemView) (name : Name) : Option Nat :=
  view.binders.findIdx? fun binder => sameVisibleName binder.name name

private def inferNewBinder (state : ReformState) (oldName : Name)
    (binderIndex : Nat) (replacement : TSyntax `term) : CommandElabM Name := do
  let candidates ← newBinderCandidates state.view oldName replacement.raw
  if candidates.isEmpty then
    throwErrorAt replacement
      "cannot determine the new optimization variable; the substitution expression must contain one new identifier"
  let usedCandidates ← withTypedPresentation state fun presentation =>
    withPresentationBinders presentation fun binderTypes binders =>
      withViewDefinitions state.view fun definitions => do
      let candidateDeclarations := candidates.map fun name =>
        (name, binderTypes[binderIndex]!)
      withLocalDeclsDND candidateDeclarations fun candidateFVars => do
        let expression ← elabPresentationTerm replacement (binders ++ definitions)
          (some binderTypes[binderIndex]!)
        pure <| candidates.zip candidateFVars |>.filterMap fun (name, fvar) =>
          if expression.containsFVar fvar.fvarId! then some name else none
  if (← get).messages.hasErrors then
    throwAbortCommand
  match usedCandidates.toList with
  | [name] => pure name
  | [] =>
      throwErrorAt replacement
        "cannot determine the new optimization variable; the substitution expression must contain one new identifier"
  | names =>
      throwErrorAt replacement
        "ambiguous substitution: expected exactly one new optimization variable, found {names}"

/-- Retain displayed binding identities in replacement syntax. Inline model definitions
only when their values and types are independent of the replaced variable. -/
private def expandReplacementDefinitions (state : ReformState) (binderIndex : Nat)
    (newName scopedNewName : Name) (replacement : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  withTypedPresentation state fun presentation =>
    withPresentationBinders presentation fun binderTypes binders =>
      withViewDefinitions state.view fun definitions =>
        withLocalDeclD newName binderTypes[binderIndex]! fun candidate => do
          let expression ← elabPresentationTerm replacement (binders ++ definitions)
            (some binderTypes[binderIndex]!)
          for definition in definitions, view in state.view.definitions do
            if expression.containsFVar definition.fvarId! &&
                (← Morew.Elab.Expr.depends binders[binderIndex]! definition) then
              throwErrorAt replacement
                "substitution replacement uses model-local definition `{view.name.eraseMacroScopes}`, which depends on the optimization variable being replaced"
          if ← Morew.Elab.Expr.depends binders[binderIndex]! expression then
            throwErrorAt replacement
              "substitution replacement depends on the optimization variable being replaced"
          let mut expression := expression
          for definition in definitions.reverse do
            let some value := (← definition.fvarId!.getDecl).value?
              | throwError "internal error: a model-local definition is not let-bound"
            expression := expression.replaceFVar definition value
          let names := binders.mapIdx fun index binder =>
            (binder.fvarId!, presentation.binders[index]!.name)
          return ⟨← delabPresentationTerm expression
            (names.push (candidate.fvarId!, scopedNewName))⟩

/-- Substitute the selected free variable while preserving lexical binders and globals.
Rebuild sequential definitions so later dependent types and bodies use substituted bindings. -/
private def substitutePresentation (state : ReformState) (binderIndex : Nat)
    (newName : Name) (replacement : TSyntax `term) :
    CommandElabM Morew.Syntax.ProblemView :=
  withTypedPresentation state fun presentation =>
    withPresentationBinders presentation fun binderTypes binders =>
      withViewDefinitions state.view fun definitions => do
        let elaborate (term : Lean.Syntax) (type : Expr) : TermElabM Expr := do
          let expression ← elabTermEnsuringType term type
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars expression
        -- Elaborate original bodies before introducing replacement definitions with the same names.
        let objective ← elaborate state.view.objective presentation.valueType
        let constraints ← state.view.constraints.mapM fun constraint =>
          elaborate constraint.proposition (mkSort Level.zero)
        withLocalDeclD newName binderTypes[binderIndex]! fun candidate => do
          let replacement ← elaborate replacement binderTypes[binderIndex]!
          let names := binders.mapIdx fun index binder =>
            if index == binderIndex then (candidate.fvarId!, newName)
            else (binder.fvarId!, presentation.binders[index]!.name)
          let rec visit (remaining : List (Morew.Syntax.DefinitionView × Expr))
              (oldBindings newBindings : Array Expr)
              (names : Array (FVarId × Name))
              (rewritten : Array Morew.Syntax.DefinitionView) :
              TermElabM Morew.Syntax.ProblemView := do
            let substExpr (expression : Expr) := expression.replaceFVars oldBindings newBindings
            match remaining with
            | [] =>
                let objective ← delabPresentationTerm (substExpr objective) names
                let constraints ← state.view.constraints.mapIdxM fun index constraint => do
                  return { constraint with
                    proposition := ← delabPresentationTerm (substExpr constraints[index]!) names }
                let oldBinder := state.view.binders[binderIndex]!
                return { state.view with
                  binders := state.view.binders.set! binderIndex { oldBinder with name := newName }
                  definitions := rewritten
                  objective
                  constraints }
            | (view, original) :: remaining =>
                let declaration ← original.fvarId!.getDecl
                let some value := declaration.value?
                  | throwError "internal error: a model-local definition is not let-bound"
                let type := substExpr declaration.type
                let value := substExpr value
                let typeSyntax ← delabPresentationTerm type names
                let view := { view with
                  value := ← delabPresentationTerm value names
                  typeSyntax? := view.typeSyntax?.map fun _ => typeSyntax
                  inferredTypeSyntax? := some typeSyntax }
                withLetDecl view.name type value fun binding =>
                  visit remaining (oldBindings.push original) (newBindings.push binding)
                    (names.push (binding.fvarId!, view.name)) (rewritten.push view)
          visit (state.view.definitions.zip definitions).toList
            #[binders[binderIndex]!] #[replacement] names #[]

private def constraintIsTypedTrue (state : ReformState)
    (index : Nat) : CommandElabM Bool :=
  withTypedPresentation state fun presentation =>
    withLocalDeclD `point presentation.domainType fun point =>
      isDefEq (mkApp presentation.constraints[index]!.predicate point) (mkConst ``True)

/-- Discharge transformed rows using unconditional image facts and retain their normalization
proofs. Coverage alone does not establish image properties. -/
private def independentTrueNormalization (state : ReformState)
    (view : Morew.Syntax.ProblemView) (index : Nat) :
    CommandElabM (Option (TSyntax `term)) :=
  withTypedPresentation state fun presentation => do
    let presentation := { presentation with
      binders := presentation.binders.mapIdx fun i binder =>
        { binder with name := view.binders[i]!.name } }
    withPresentationBinders presentation fun _ binders =>
      withViewDefinitions view fun definitions => do
        let proposition ← elabTermEnsuringType view.constraints[index]!.proposition
          (mkSort Level.zero)
        synthesizeSyntheticMVarsNoPostponing
        let proposition ← instantiateMVars proposition
        -- Expand predicate definitions before applying rewrite theorems with checked operation instances.
        let body ← Morew.Elab.Substitution.Evidence.predicateView proposition 32
        let mut theorems : SimpTheorems := {}
        for name in #[``Real.exp_pos, ``sq_nonneg, ``true_and, ``and_true] do
          theorems ← theorems.addConst name
        let context ← Simp.mkContext (simpTheorems := #[theorems])
          (congrTheorems := ← getSimpCongrTheorems)
        let (result, _) ← Simp.main body context (methods := Simp.mkDefaultMethodsCore #[])
        unless result.expr.isConstOf ``True do return none
        let proof ← result.getProof
        let equality ← mkEq proposition (mkConst ``True)
        unless ← isDefEq (← inferType proof) equality do return none
        let proof := mkExpectedPropHint proof equality
        let proof ← mkLetFVars definitions proof
        let proof ← mkLambdaFVars binders proof (usedOnly := true)
        let proof ← mkLambdaFVars (← getLCtx).getFVars proof (usedOnly := true)
        checkWithKernel proof
        return some (← exactExpressionSyntax proof)

/-- Preserve a definition block when it contains proofs or types depending on the replaced
decision. Relate the retained presentation to the canonical target by normalization. -/
private def preserveDefinitionExpressions (state : ReformState)
    (binderIndex : Nat) : CommandElabM Bool := do
  if state.view.definitions.isEmpty then return false
  withTypedPresentation state fun presentation =>
    withPresentationBinders presentation fun _ binders =>
      withViewDefinitions state.view fun definitions => do
        definitions.anyM fun definition => do
          return (← isProof definition) ||
            (← Morew.Elab.Expr.depends binders[binderIndex]! (← inferType definition))

/-- Check the complete proposed presentation before retaining simplifications of dependent
expressions. Restore declarations, messages, and elaboration state after the check. -/
private def simplifiedPresentationCheck (state : ReformState)
    (view : Morew.Syntax.ProblemView) :
    CommandElabM Bool :=
  withTypedPresentation state fun presentation => do
    let saved ← Term.saveState
    try
      withoutErrToSorry do
        let term ← liftMacroM view.toTermSyntax
        let type ← mkAppM ``Morew.Problem
          #[presentation.domainType, presentation.valueType]
        let value ← elabTermEnsuringType term type
        synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
          checkWithKernel value
        pure !(← getThe Core.State).messages.hasErrors
    catch exception =>
      if exception.isInterrupt || exception.isMaxRecDepth || exception.isMaxHeartbeat then
        throw exception
      pure false
    finally
      saved.restore (restoreInfo := true)
      setEnv saved.meta.core.env

/-- Certify the coordinate map from current source feasibility, preserving unselected coordinates. -/
private def parameterizationCertificate (state : ReformState)
    (ref : Lean.Syntax)
    (oldName newName : Name) (binderIndex : Nat) (replacement mapTerm : TSyntax `term)
    (selectedRule? : Option (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  try
    runTermElabM fun sectionFVars => do
      let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
      let presentation := typed.presentation
      let binderTypes := presentation.binders.map (·.type)
      let split ← Morew.Elab.Substitution.Coordinates.split
        typed.semanticDomainType binderTypes binderIndex
      let splitType ← whnf (← inferType split)
      let retainedType := splitType.getAppArgs[1]!.getAppArgs[0]!
      -- These temporary model binders leave scope before evidence is searched.
      let map ← withPresentationBinders presentation fun _ binders =>
        withLocalDeclD newName binderTypes[binderIndex]! fun fresh => do
          let replacement ← elabPresentationTerm replacement (binders.push fresh)
            (some binderTypes[binderIndex]!)
          synthesizeSyntheticMVarsNoPostponing
          let replacement ← instantiateMVars replacement
          withLocalDeclD `retained retainedType fun retained =>
            withLocalDeclD `coordinate binderTypes[binderIndex]! fun coordinate => do
              let mut arguments := #[]
              let mut retainedIndex := 0
              for index in [:binders.size] do
                if index == binderIndex then arguments := arguments.push coordinate
                else
                  arguments := arguments.push (← Morew.Elab.Substitution.Coordinates.project
                    retained retainedIndex (binders.size - 1))
                  retainedIndex := retainedIndex + 1
              let body := replacement.replaceFVars (binders.push fresh)
                (arguments.push coordinate)
              mkLambdaFVars #[retained, coordinate] body
      let fullMap ← elabTermEnsuringType mapTerm
        (← mkArrow typed.semanticDomainType typed.semanticDomainType)
      synthesizeSyntheticMVarsNoPostponing
      let fullMap ← instantiateMVars fullMap
      let expectedRuleType ← mkAppM ``Morew.CoordinateParameterization #[map]
      let selection ← match selectedRule? with
        | none => pure (none, none)
        | some ruleSyntax => do
          if ruleSyntax.raw.isIdent then
            if let some (.const name _) ← resolveId? ruleSyntax (withInfo := true) then
              pure (none, some name)
            else
              let rule ← elabTermEnsuringType ruleSyntax expectedRuleType
              synthesizeSyntheticMVarsNoPostponing
              pure (some (← instantiateMVars rule), none)
          else
            let rule ← elabTermEnsuringType ruleSyntax expectedRuleType
            synthesizeSyntheticMVarsNoPostponing
            pure (some (← instantiateMVars rule), none)
      let proof ← withLocalDeclD `sourcePoint typed.semanticDomainType fun point => do
        let feasibleType ← mkAppM ``Morew.Problem.feasible #[typed.semantic, point]
        withLocalDeclD `sourceFeasible feasibleType fun feasible => do
          let canonicalEvidence ← mkAppM ``Iff.mp
            #[mkApp typed.normalization.feasibleIff point, feasible]
          let coordinates ← whnf (← mkAppM ``Equiv.toFun #[split, point])
          let retained ← Morew.Elab.Rewrite.Registry.structural (mkProj ``Prod 0 coordinates)
          let selected ← Morew.Elab.Rewrite.Registry.structural (mkProj ``Prod 1 coordinates)
          let accept (result : Morew.Elab.Substitution.Match.Result) : MetaM Expr := do
            let coverage ← mkLambdaFVars #[point, feasible] result.rangeProof
            let proof ← mkAppM ``Morew.CoordinateParameterization.toFeasibleSurjection
              #[result.rule, typed.semantic, split, split, coverage]
            let expected ← mkAppM ``Morew.FeasibleSurjection #[typed.semantic, fullMap]
            unless ← isDefEq (← inferType proof) expected do
              throwError "coordinate parameterization does not preserve the complete decision tuple"
            checkWithKernel proof
            return proof
          match selection with
          | (some rule, _) =>
            Morew.Elab.Substitution.Match.rule
              map point retained selected canonicalEvidence rule accept
          | (_, some name) =>
            Morew.Elab.Substitution.Match.declaration
              map point retained selected canonicalEvidence name accept
          | _ =>
            Morew.Elab.Substitution.Match.discover
              map point retained selected canonicalEvidence accept
      -- Store the certificate once within the command transaction.
      let name ← mkAuxDeclName (kind := `substitution)
      let proof ← mkAuxDefinitionFor name proof (zetaDelta := true) (compile := false)
      modifyEnv (addNoncomputable · name)
      exactExpressionSyntax proof
  catch
    | .error _ message =>
      throwErrorAt ref
        "substitution of `{oldName.eraseMacroScopes}` by `{(ref.reprint.getD "<replacement>").trimAscii.toString}`: {message}"
    | exception => throw exception

/-- Check explicit coverage against the elaborated map before constructing its pullback. -/
private def explicitSubstitutionCertificate (state : ReformState)
    (mapTerm provided : TSyntax `term) : CommandElabM (TSyntax `term) :=
  runTermElabM fun sectionFVars => withoutErrToSorry do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let map ← elabTermEnsuringType mapTerm
      (← mkArrow typed.semanticDomainType typed.semanticDomainType)
    synthesizeSyntheticMVarsNoPostponing
    let map ← instantiateMVars map
    let expected ← mkAppM ``Morew.FeasibleSurjection #[typed.semantic, map]
    let proof ← elabTermEnsuringType provided expected
    synthesizeSyntheticMVarsNoPostponing
    if (← getThe Core.State).messages.hasErrors then throwAbortTerm
    let proof ← instantiateMVars proof
    if proof.hasMVar || proof.hasSorry then
      throwErrorAt provided "substitution coverage contains incomplete evidence"
    withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
      checkWithKernel proof
    let name ← mkAuxDeclName (kind := `substitution)
    -- Retain the checked source and map despite aliases in the certificate's inferred type.
    let proof ← mkAuxDefinition name (← instantiateMVars expected) proof
      (zetaDelta := true) (compile := false)
    modifyEnv (addNoncomputable · name)
    exactExpressionSyntax proof

private def materializeSubstitution (state : ReformState) (_step : Lean.Syntax)
    (replacement : TSyntax `term)
    (providedCertificate? : Option (TSyntax `term))
    (selectedRule? : Option (TSyntax `term))
    (oldName : Name) (binderIndex : Nat)
    (allocation : Morew.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some newName := allocation.findName? 0
    | throwErrorAt replacement "internal error: missing substitution binder allocation"
  let scopedNewName ← withFreshMacroScope do
    MonadQuotation.addMacroScope newName
  let replacementRef := replacement.raw
  let replacement ← expandReplacementDefinitions state binderIndex
    newName scopedNewName replacement

  let oldBinder := state.view.binders[binderIndex]!
  let newBinders := state.view.binders.set! binderIndex {
    oldBinder with name := scopedNewName
  }
  let mut normalizationLemmas := state.normalizationLemmas

  let binderNames := newBinders.map fun binder => binder.name
  let domainType := state.semanticDomainType
  let domainPattern ← liftMacroM <| mkProductPattern binderNames
  let mapComponents : Array (TSyntax `term) := state.view.binders.mapIdx fun i binder =>
    if i == binderIndex then replacement else ⟨mkIdent binder.name⟩
  let mapResult ← liftMacroM <| mkProduct mapComponents
  let mapTerm ← liftMacroM `(fun ($domainPattern : $domainType) => $mapResult)
  -- Resolve the pattern lambda before certificate comparisons can unfold the objective.
  let mapTerm ← runTermElabM fun _ => do
    let domain ← elabType domainType
    let map ← elabTermEnsuringType mapTerm (← mkArrow domain domain)
    synthesizeSyntheticMVarsNoPostponing
    exactExpressionSyntax (← instantiateMVars map)

  let stepCertificate ← match providedCertificate? with
    | some proofTerm =>
        explicitSubstitutionCertificate state mapTerm proofTerm
    | none =>
        parameterizationCertificate state replacementRef oldName scopedNewName binderIndex
          replacement mapTerm selectedRule?

  let substitutedView ← substitutePresentation state binderIndex scopedNewName replacement
  let substitutedObjective := substitutedView.objective
  let objective ← liftMacroM <| simplifyExpLog substitutedObjective
  let preserveDefinitions ← preserveDefinitionExpressions state binderIndex
  let substitutedDefinitions := substitutedView.definitions
  let definitions ← if preserveDefinitions || substitutedDefinitions.isEmpty then
      pure substitutedDefinitions
    else do
      substitutedDefinitions.mapM fun definition => do
        let simplify (term : Lean.Syntax) : CommandElabM Lean.Syntax :=
          liftMacroM <| simplifyExpLog term
        let value ← simplify definition.value
        let typeSyntax? ← definition.typeSyntax?.mapM simplify
        let inferredTypeSyntax? ← definition.inferredTypeSyntax?.mapM simplify
        pure { definition with value, typeSyntax?, inferredTypeSyntax? }
  let mut constraints : Array Morew.Syntax.ConstraintView := #[]
  let mut substitutedConstraints : Array Morew.Syntax.ConstraintView := #[]
  let mut liveCheckpointRows : Array Nat := #[]
  let mut removedCheckpointRows := state.removedCheckpointRows
  for index in [:state.view.constraints.size] do
    let constraint := state.view.constraints[index]!
    let checkpointIndex := state.liveCheckpointRows[index]!
    let wasPresentedAsTrue ← constraintIsTypedTrue state index
    let substitutedProposition := substitutedView.constraints[index]!.proposition
    let proposition ← liftMacroM <| simplifyExpLog substitutedProposition
    let normalization? ← independentTrueNormalization state substitutedView index
    let provedTrue := normalization?.isSome
    if let some proof := normalization? then
      normalizationLemmas := normalizationLemmas.push proof
    if provedTrue && !wasPresentedAsTrue then
      removedCheckpointRows := removedCheckpointRows.insert checkpointIndex
    else
      liveCheckpointRows := liveCheckpointRows.push checkpointIndex
      constraints := constraints.push { constraint with proposition }
      substitutedConstraints := substitutedConstraints.push
        { constraint with proposition := substitutedProposition }
  let simplifiedView : Morew.Syntax.ProblemView := {
    state.view with
    binders := newBinders
    definitions
    objective
    constraints
  }
  let newView ← if ← simplifiedPresentationCheck state simplifiedView then
      pure simplifiedView
    else
      -- Preserve dependent definitions and the normalization evidence for removed positivity rows.
      pure { simplifiedView with
        definitions := substitutedDefinitions
        objective := substitutedObjective
        constraints := substitutedConstraints }

  let current := state.semantic
  let nextSemantic ← liftMacroM `(Morew.Problem.pullback $current $mapTerm)
  let primitiveEquiv ← liftMacroM `(
    Morew.pullbackEquiv $current $mapTerm $stepCertificate)
  let primitive ← liftMacroM <|
    liftCertificateEquiv state.runner primitiveEquiv
  pure {
    view := newView
    semantic := nextSemantic
    semanticDomainType := state.semanticDomainType
    primitiveCertificate := primitive
    simplifyExpLogTerms := true
    hasSubstitution := true
    liveCheckpointRows
    removedCheckpointRows
    normalizationLemmas
  }

/-- Prepare a substitution and construct it after checking the requested names. -/
def prepareSubstitution (state : ReformState) (step : Lean.Syntax)
    (oldIdent : TSyntax `ident) (replacement : TSyntax `term)
    (providedCertificate? : Option (TSyntax `term))
    (selectedRule? : Option (TSyntax `term) := none) :
    CommandElabM SurfaceStepDraft := do
  let replacement : TSyntax `term :=
    ⟨← liftTermElabM <| preResolveReplacement state.view replacement.raw⟩
  let oldName := oldIdent.getId
  let some binderIndex := findBinderIndex state.view oldName
    | throwErrorAt oldIdent "unknown optimization variable `{oldName.eraseMacroScopes}`"
  let newName ← inferNewBinder state oldName binderIndex replacement
  let request : Morew.Elab.Reformulation.NameRequest := {
    id := 0
    kind := .inferredDecisionBinder
    requested := newName
    ref := replacement.raw
  }
  pure {
    nameRequests := #[request]
    materialize := fun allocation =>
      materializeSubstitution state step replacement providedCertificate? selectedRule?
        oldName binderIndex allocation
  }

@[morew_reformulation_step Morew.substituteStep]
private def elabSubstitution : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| substitute $oldName:ident := $replacement:term
      $[using $provided:term]?) =>
      prepareSubstitution state step oldName replacement provided
  | _ => throwUnsupportedSyntax

@[morew_reformulation_step Morew.substituteViaStep]
private def elabSubstitutionVia : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| substitute $oldName:ident := $replacement:term via $rule:term) =>
      prepareSubstitution state step oldName replacement none (some rule)
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
