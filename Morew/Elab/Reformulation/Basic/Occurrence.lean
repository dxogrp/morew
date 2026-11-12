/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Reformulation.Rows
import Morew.Elab.Rewrite.Plan
import Morew.Elab.Reformulation.Syntax
import Morew.Transform.Context
import Morew.Elab.ObjectiveContext
import Morew.Elab.Expr

/-! Select occurrences before reducing model-local definitions. Named selectors use
binding identity; expression selectors compare rigid typed terms. Check the selected
context and resulting presentation against the current problem. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

-- Select computational and logical operands; exclude type, proof, and instance arguments.
private partial def replaceOccurrence (expression needle hole : Expr) (predicate := false) :
    StateT Nat MetaM Expr := do
  if ← Morew.Elab.ObjectiveContext.sameExpression expression needle then
    modify (· + 1)
    return hole
  match expression with
  | .mdata data body => return .mdata data (← replaceOccurrence body needle hole predicate)
  | .app .. =>
      let function := expression.getAppFn
      let arguments := expression.getAppArgs
      let info ← getFunInfoNArgs function arguments.size
      let head := function.consumeMData
      let function ← if head.isFVar || head.isLambda || head.isLet then
          replaceOccurrence function needle hole predicate
        else pure function
      let mut updated := #[]
      for argument in arguments, index in [:arguments.size] do
        let parameter := info.paramInfo[index]?
        let argumentType ← inferType argument
        if (parameter.any fun parameter =>
            parameter.binderInfo.isInstImplicit || parameter.isInstance) ||
            (← isProof argument) || (← isClass? argumentType).isSome then
          -- Exclude explicit class operands' instance contents.
          updated := updated.push argument
        else
          -- Visit logical predicates unless later proofs or instances depend on their types.
          let predicateArgument ← if predicate && !(parameter.any (·.hasFwdDeps)) then
              isPropFormerType argumentType
            else pure false
          if !predicateArgument && (← isTypeFormer argument) then
            updated := updated.push argument
          else
            -- Traverse predicate operands through computational containers.
            updated := updated.push
              (← replaceOccurrence argument needle hole predicate)
      return mkAppN function updated
  | .lam name type body info =>
      let count ← get
      let (result, count) ← withLocalDecl name info type fun binding => do
        let (body, count) ← (replaceOccurrence (body.instantiate1 binding) needle hole predicate).run count
        return (← mkLambdaFVars #[binding] body, count)
      set count
      return result
  | .forallE name type body info =>
      -- Visit independent implication antecedents; preserve dependent proof-binder types.
      let type ← if predicate && !info.isInstImplicit && !body.hasLooseBVar 0 &&
          (← isProp type) then
          replaceOccurrence type needle hole true
        else pure type
      let count ← get
      let (result, count) ← withLocalDecl name info type fun binding => do
        let (body, count) ← (replaceOccurrence (body.instantiate1 binding) needle hole predicate).run count
        return (← mkForallFVars #[binding] body, count)
      set count
      return result
  | .letE name type value body _ =>
      let predicateValue ← if predicate then isPropFormerType type else pure false
      let value ← if (← isProof value) || (← isClass? type).isSome ||
          (!predicateValue && (← isTypeFormer value)) then pure value
        else replaceOccurrence value needle hole predicate
      let count ← get
      let (result, count) ← withLetDecl name type value fun binding => do
        let (body, count) ← (replaceOccurrence (body.instantiate1 binding) needle hole predicate).run count
        return (← mkLetFVars #[binding] body (usedLetOnly := false), count)
      set count
      return result
  | .proj name index value =>
      let value ← if (← isClass? (← inferType value)).isSome then pure value
        else replaceOccurrence value needle hole predicate
      return .proj name index value
  | other => return other

private def closeBody (domain : Expr) (binders definitions : Array Expr)
    (body : Expr) : MetaM Expr := do
  let body ← mkLetFVars definitions body (usedLetOnly := false)
  withLocalDeclD `point domain fun point => do
    let components ← pointComponents point binders.size
    mkLambdaFVars #[point] (body.replaceFVars binders components)

private structure SelectedOccurrence where
  view : Morew.Syntax.ProblemView
  auxiliaryType : Expr
  selected : Expr
  context : Expr
  deriving Inhabited

private def selectOccurrence (state : ReformState) (presentation : PresentationState)
    (selector : TSyntax `boundOccurrence) (row? : Option Nat)
    (binderName boundName : Name) (direction : Morew.BoundDirection) :
    TermElabM SelectedOccurrence :=
  withPresentationBinders presentation fun _ binders =>
  withViewDefinitions state.view fun definitions => do
    let location := row?.map (state.view.constraints[·]!.proposition)
      |>.getD state.view.objective
    let expected := if row?.isSome then mkSort .zero
      else if state.view.sense == .maximize &&
          presentation.valueType.isAppOfArity ``OrderDual 1 then
        presentation.valueType.getArg! 0
      else presentation.valueType
    let body ← elabTerm location (some expected)
    synthesizeSyntheticMVarsNoPostponing
    let body ← instantiateMVars body
    let needle ← match selector with
      | `(boundOccurrence| $name:ident) =>
          let some index := state.view.definitions.findIdx? (sameVisibleName ·.name name.getId)
            | throwErrorAt name "unknown model-local definition `{name.getId.eraseMacroScopes}`"
          pure definitions[index]!
      | `(boundOccurrence| ($term:term)) =>
          elabPresentationTerm term (binders ++ definitions)
      | _ => throwUnsupportedSyntax
    if (← Morew.Elab.Expr.hasUnresolvedStrict body) ||
        (← Morew.Elab.Expr.hasUnresolvedStrict needle) || body.hasSorry || needle.hasSorry then
      throwErrorAt selector "occurrence selection contains unresolved metavariables"
    if (← isType needle) || (← isProof needle) then
      throwErrorAt selector "an occurrence bound requires a value, not a type or proof"
    let auxiliaryType ← zetaReduce (← inferType needle)
    for binding in binders do
      if ← Morew.Elab.Expr.depends binding auxiliaryType then
        throwErrorAt selector "the selected type depends on an optimization variable; dependent auxiliaries are unsupported"
    let preorderType ← mkAppM ``Preorder #[auxiliaryType]
    let preorder ← synthInstance preorderType
    let preorder ← zetaReduce preorder
    for binding in binders do
      if ← Morew.Elab.Expr.depends binding preorder then
        throwErrorAt selector "the selected order instance depends on an optimization variable"
    withLocalDeclD binderName auxiliaryType fun auxiliary => do
      let (replaced, count) ← (replaceOccurrence body needle auxiliary row?.isSome).run 0
      if count == 0 then
        throwErrorAt selector "selector has no direct occurrence in the selected location"
      if count > 1 then
        throwErrorAt selector "ambiguous occurrence selector: found {count} occurrences in the selected location"
      let names := (binders.mapIdx fun i binding =>
        (binding.fvarId!, state.view.binders[i]!.name)) ++
        (definitions.mapIdx fun i binding =>
          (binding.fvarId!, state.view.definitions[i]!.name)) ++
        #[(auxiliary.fvarId!, binderName)]
      let replacementSyntax ← delabPresentationTerm replaced names
      let selectedSyntax ← delabPresentationTerm needle names
      let boundTerm : TSyntax `term := ⟨mkIdent binderName⟩
      let selectedTerm : TSyntax `term := ⟨selectedSyntax⟩
      let proposition ← match direction with
        | .upper => `($selectedTerm ≤ $boundTerm)
        | .lower => `($boundTerm ≤ $selectedTerm)
      let mut view := { state.view with
        binders := state.view.binders.push {
          name := binderName
          typeSyntax := ← presentationTypeSyntax auxiliaryType } }
      if let some index := row? then
        view := { view with constraints := view.constraints.modify index (fun entry =>
          { entry with proposition := replacementSyntax }) }
      else
        view := { view with objective := replacementSyntax }
      view := { view with constraints := view.constraints.push {
        name := boundName, proposition } }
      let selected ← closeBody presentation.domainType binders definitions needle
      let context ← closeBody presentation.domainType binders definitions
        (← mkLambdaFVars #[auxiliary] replaced)
      return { view, auxiliaryType, selected, context }

private def byDefinitionalEquality (type : Expr) (iff : Bool) : MetaM Expr :=
  forallTelescopeReducing type fun binders conclusion => do
    let arguments := conclusion.getAppArgs
    let body ← if iff then pure (mkApp (mkConst ``Iff.rfl) arguments[0]!)
      else mkEqRefl arguments[1]!
    unless ← isDefEq (← inferType body) conclusion do
      throwError "selected context does not reconstruct the original location"
    mkLambdaFVars binders body

private def automaticCertificate (type : Expr) (constraint : Bool)
    (_sense : Morew.ObjectiveSense) : TermElabM Expr := do
  let type ← whnf type
  let constructor := if constraint then ``Morew.ConstraintBoundContext.mk
    else ``Morew.ObjectiveBoundContext.mk
  let application := mkAppN (mkConst constructor type.getAppFn.constLevels!) type.getAppArgs
  let .forallE _ atValueType remaining _ ← whnf (← inferType application)
    | throwError "invalid bound-context certificate type"
  let atValue ← byDefinitionalEquality atValueType constraint
  let .forallE _ backwardType _ _ ← whnf (remaining.instantiate1 atValue)
    | throwError "invalid bound-context certificate fields"
  let backward ← forallTelescopeReducing backwardType fun arguments conclusion => do
    let point := arguments[0]!
    let bound := arguments[3]!
    let proof ← if constraint then do
        let given := arguments[4]!
        Morew.Elab.ObjectiveContext.provePredicate point
          (← simpOnly (← inferType given)) (← simpOnly conclusion) bound given
      else do
        let conclusion ← simpOnly conclusion
        let args := conclusion.getAppArgs
        unless conclusion.isAppOfArity ``LE.le 4 do
          throwError "automatic context analysis requires an ordered scalar objective; provide `using`"
        let left := args[2]!
        let right := args[3]!
        let canonical := mkApp4 (mkConst ``LE.le [.zero])
          (mkConst ``Real) (mkConst ``Real.instLE) left right
        if ← isDefEq canonical conclusion then
          Morew.Elab.ObjectiveContext.proveInequality point left right bound
        else
          let reversed := mkApp4 (mkConst ``LE.le [.zero])
            (mkConst ``Real) (mkConst ``Real.instLE) right left
          unless ← isDefEq reversed conclusion do
            throwError "automatic context analysis requires the canonical real order; provide `using`"
          Morew.Elab.ObjectiveContext.proveInequality point right left bound
    let proof ← match proof with
      | .ok proof => pure proof
      | .error reason => throwError reason
    unless ← isDefEq (← inferType proof) conclusion do
      throwError "automatic context evidence does not match the selected bound"
    mkLambdaFVars arguments proof
  let result := mkApp2 application atValue backward
  checkWithKernel result
  return result

private def proveRearrangement (type : Expr) : TermElabM Expr := do
  let proof ← elabTermEnsuringType (← `(by
    intro point
    dsimp only [Morew.Problem.objectiveBoundAt, Morew.Problem.constraintBoundAt,
      Morew.BoundDirection.Rel, Morew.Problem.objective, Morew.Problem.feasible]
    simp only [and_assoc, and_left_comm, and_comm, true_and, and_true])) type
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

private def makeDecomposition (presentation : PresentationState) (index : Nat)
    (sourceProblem : Expr) : TermElabM Expr := do
  let rows := presentation.constraints.map (·.predicate)
  let remainder ← mkFeasibleFunction presentation.domainType
    (rows.extract 0 index ++ rows.extract (index + 1) rows.size)
  let source := rows[index]!
  let feasible ← mkAppM ``Morew.Problem.feasible #[sourceProblem]
  let proofType ← withLocalDeclD `point presentation.domainType fun point => do
    let rhs := mkApp2 (mkConst ``And) (mkApp remainder point) (mkApp source point)
    mkForallFVars #[point] (mkApp2 (mkConst ``Iff) (mkApp feasible point) rhs)
  let proof ← proveRearrangement proofType
  mkAppM ``Morew.ConstraintDecomposition.mk #[remainder, proof]

private def materializeOccurrenceBound (state : ReformState)
    (selector : TSyntax `boundOccurrence) (row? : Option Nat)
    (provided? : Option (TSyntax `term)) (direction : Morew.BoundDirection)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionVars => withoutErrToSorry do
    -- Instantiate assigned universe and instance metavariables in section-local types.
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionVars
    let some binderName := allocation.findName? 0
      | throwError "missing occurrence auxiliary name"
    let some boundName := allocation.findName? 1
      | throwError "missing occurrence bound name"
    let binderName ← withFreshMacroScope do MonadQuotation.addMacroScope binderName
    let selected ← selectOccurrence state typed.presentation selector row? binderName boundName direction
    -- Select from retained definitions and prove agreement with the normalized current problem.
    let source ← if state.view.definitions.isEmpty then pure typed.canonical else do
      let sourceSyntax ← liftMacroM state.view.toTermSyntax
      elabTermEnsuringType sourceSyntax (← inferType typed.canonical)
    synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceEquiv ← if ← isDefEq typed.canonical source then
        mkAppM ``Morew.GlobalEquiv.refl #[typed.canonical]
      else do
        let normalization ← checkedPointwiseNormalization state.sourceName
          typed.canonical source state.normalizationLemmas
        pure normalization.equiv
    let sourcePresentation ← typedPresentationFromExpression source state.view
    let direction := Lean.mkConst <| match direction with
      | .upper => ``Morew.BoundDirection.upper
      | .lower => ``Morew.BoundDirection.lower
    let decomposition? ← row?.mapM (makeDecomposition sourcePresentation · source)
    let certificateType ← if let some decomposition := decomposition? then do
        let remainder ← mkProjection decomposition `remainder
        mkAppM ``Morew.ConstraintBoundContext
          #[remainder, sourcePresentation.constraints[row?.get!]!.predicate,
            selected.selected, selected.context, direction]
      else
        mkAppM ``Morew.ObjectiveBoundContext
          #[source, selected.selected, selected.context, direction]
    let contextProof ← match provided? with
      | some proof => elabTermEnsuringType proof certificateType
      | none => automaticCertificate certificateType row?.isSome state.view.sense
    synthesizeSyntheticMVarsNoPostponing
    let contextProof ← instantiateMVars contextProof
    if contextProof.hasMVar || contextProof.hasSorry then
      throwError "bound context certificate contains incomplete evidence"
    checkWithKernel contextProof
    let equiv ← if let some decomposition := decomposition? then
        mkAppM ``Morew.constraintBoundAtEquiv
          #[source, decomposition, selected.selected, selected.context, direction, contextProof]
      else
        mkAppM ``Morew.objectiveBoundAtEquiv
          #[source, selected.selected, selected.context, direction, contextProof]
    let naturalType ← whnf (← inferType equiv)
    let natural := naturalType.getAppArgs.back!
    let targetSyntax ← liftMacroM selected.view.toTermSyntax
    let target ← elabTerm targetSyntax (some (← inferType natural))
    synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars target
    let targetType ← whnf (← inferType target)
    let nextDomain := targetType.getAppArgs[0]!
    let objectiveEquality ← withLocalDeclD `point nextDomain fun point => do
      let left ← mkAppM ``Morew.Problem.objective #[natural, point]
      let right ← mkAppM ``Morew.Problem.objective #[target, point]
      unless ← isDefEq left right do
        throwError "occurrence lift changed the objective outside the selected location"
      mkLambdaFVars #[point] (← mkEqRefl left)
    let feasibleType ← withLocalDeclD `point nextDomain fun point => do
      let left ← mkAppM ``Morew.Problem.feasible #[natural, point]
      let right ← mkAppM ``Morew.Problem.feasible #[target, point]
      mkForallFVars #[point] (mkApp2 (mkConst ``Iff) left right)
    let normalization ← mkAppM ``Morew.pointwiseEquiv
      #[natural, target, objectiveEquality, ← proveRearrangement feasibleType]
    let equiv ← mkAppM ``Morew.GlobalEquiv.trans #[equiv, normalization]
    let equiv ← mkAppM ``Morew.GlobalEquiv.trans
      #[sourceEquiv, equiv]
    let equiv ← mkAppM ``Morew.GlobalEquiv.trans
      #[typed.normalization.equiv, equiv]
    let primitive ← state.runner.liftEquiv equiv
    let primitive ← instantiateMVars primitive
    checkWithKernel primitive
    -- Store the certificate as a constant to avoid repeated proof elaboration.
    let primitiveName ← mkAuxDeclName (kind := `_occurrenceCertificate)
    let primitive ← mkAuxDefinitionFor primitiveName primitive (zetaDelta := true)
      (compile := false)
    modifyEnv (addNoncomputable · primitiveName)
    let semantic ← exactExpressionSyntax target
    return {
      view := selected.view
      semantic
      semanticDomainType := ← exactExpressionSyntax nextDomain
      primitiveCertificate := ← exactExpressionSyntax primitive
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      liveCheckpointRows := Array.range selected.view.constraints.size
      removedCheckpointRows := {}
      normalizationLemmas := state.normalizationLemmas
      checkpoint? := some { semantic, semanticAnchor := semantic, view := selected.view }
    }

/-- Plan a bound at one objective or constraint occurrence. -/
def prepareOccurrenceBound (state : ReformState) (_step : Syntax)
    (binder : TSyntax `ident) (selector : TSyntax `boundOccurrence)
    (constraint? explicitLabel? : Option (TSyntax `ident))
    (provided? : Option (TSyntax `term)) (direction : Morew.BoundDirection) :
    CommandElabM SurfaceStepDraft := do
  let row? ← constraint?.mapM (Rows.findConstraint state)
  -- Use the surrounding context's certificate to determine bound direction.
  let stem := if direction == .upper then "epigraph" else "hypograph"
  let defaultName := Name.mkSimple s!"{stem}_{binder.getId.eraseMacroScopes}"
  let boundName := explicitLabel?.map (·.getId.eraseMacroScopes) |>.getD defaultName
  return {
    nameRequests := #[
      { id := 0, kind := .explicitDecisionBinder, requested := binder.getId, ref := binder.raw },
      { id := 1, kind := if explicitLabel?.isSome then .explicitConstraintLabel else .fixedPublicDefault,
        requested := boundName, ref := explicitLabel?.map (·.raw) |>.getD binder.raw }]
    materialize := materializeOccurrenceBound state selector row? provided? direction
  }

@[morew_reformulation_step Morew.epigraphAtStep]
private def elabEpigraphAt : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| epigraph $binder:ident at $selector:boundOccurrence
      $[in $constraint:ident]? $[as $label:ident]? $[using $provided:term]?) =>
      prepareOccurrenceBound state step binder selector constraint label provided .upper
  | _ => throwUnsupportedSyntax

@[morew_reformulation_step Morew.hypographAtStep]
private def elabHypographAt : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| hypograph $binder:ident at $selector:boundOccurrence
      $[in $constraint:ident]? $[as $label:ident]? $[using $provided:term]?) =>
      prepareOccurrenceBound state step binder selector constraint label provided .lower
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
