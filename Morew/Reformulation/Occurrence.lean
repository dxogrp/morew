import Morew.Reformulation.Presentation
import Morew.Reformulation.Syntax
import Morew.Transform.Context
import Morew.Elab.ObjectiveContext

/-!
# Bounds at selected occurrences

Selection runs before reducing model-local definitions. A named reference is
identified by its binding, while an expression selector compares rigid typed
terms. The selected context and every emitted presentation are checked against
the current semantic problem before the runner commits the step.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

-- Only computational operands and logical predicate operands are selectable.
-- Type parameters, proof arguments, and instances are not occurrences in the
-- mathematical expression, even when they contain the selected value.
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
          -- Explicit class operands carry instances too; their internals are
          -- excluded independently of how the parameter was declared.
          updated := updated.push argument
        else
          -- `Or`'s propositions and `Exists`' predicate are type-formers too.
          -- A proposition indexing a later proof or instance remains a type
          -- parameter: replacing it would also require transporting evidence.
          let predicateArgument ← if predicate && !(parameter.any (·.hasFwdDeps)) then
              isPropFormerType argumentType
            else pure false
          if !predicateArgument && (← isTypeFormer argument) then
            updated := updated.push argument
          else
            -- Computational containers may carry predicate operands, as in
            -- `(P, Q).1`. Keep predicate traversal enabled through the container.
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
      -- An independent proposition domain is an implication antecedent. A
      -- dependent proof binder keeps its original type: changing it would
      -- also require transporting uses of the bound proof in the body.
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

private partial def pointComponents (point : Expr) : Nat → MetaM (Array Expr)
  | 0 => pure #[]
  | 1 => pure #[point]
  | n + 2 => do
      let first ← mkAppM ``Prod.fst #[point]
      let last ← mkAppM ``Prod.snd #[point]
      return (← pointComponents first (n + 1)).push last

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

/-- Expose retained bindings under the names used by a new selector. Temporary
let aliases let Lean handle shadowing and projection notation normally; replacing
only these aliases afterwards preserves model-definition binding identities. -/
private partial def elabOccurrenceSelector (term : TSyntax `term) (bindings : Array Expr) :
    TermElabM Expr := do
  let names ← bindings.mapM fun binding => do
    return ((← binding.fvarId!.getDecl).userName, binding)
  let rec collect (stx : Syntax) (aliases : NameMap Expr) : NameMap Expr := Id.run do
    let mut aliases := aliases
    if let .ident _ _ name resolved := stx then
      -- A global reference captured by a macro must retain its resolution.
      unless resolved.any (fun | .decl .. => true | _ => false) do
        let reference := extractMacroScopes name
        for (name, binding) in names do
          let displayName := name.eraseMacroScopes
          if displayName.isPrefixOf reference.name then
            let aliasName := { reference with name := displayName }.review
            if aliasName != name then aliases := aliases.insert aliasName binding
    for child in stx.getArgs do
      aliases := collect child aliases
    return aliases
  let rec elaborate (remaining : List (Name × Expr)) (aliases values : Array Expr) :
      TermElabM Expr := do
    match remaining with
    | [] =>
        let expression ← elabTerm term none
        synthesizeSyntheticMVarsNoPostponing
        return (← instantiateMVars expression).replaceFVars aliases values
    | (name, value) :: remaining =>
        withLetDecl name (← inferType value) value fun temporary =>
          elaborate remaining (aliases.push temporary) (values.push value)
  elaborate (collect term.raw {}).toList #[] #[]

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
          let some index := state.view.definitions.findIdx? (sameUserName ·.name name.getId)
            | throwErrorAt name "unknown model-local definition `{name.getId.eraseMacroScopes}`"
          pure definitions[index]!
      | `(boundOccurrence| ($term:term)) =>
          elabOccurrenceSelector term (binders ++ definitions)
      | _ => throwUnsupportedSyntax
    if (← Morew.Elab.Conic.Plan.unresolved body) ||
        (← Morew.Elab.Conic.Plan.unresolved needle) || body.hasSorry || needle.hasSorry then
      throwErrorAt selector "occurrence selection contains unresolved metavariables"
    if (← isType needle) || (← isProof needle) then
      throwErrorAt selector "an occurrence bound requires a value, not a type or proof"
    let auxiliaryType ← zetaReduce (← inferType needle)
    for binding in binders do
      if ← Morew.Elab.Affine.depends binding auxiliaryType then
        throwErrorAt selector "the selected type depends on a decision variable; dependent auxiliaries are unsupported"
    let preorderType ← mkAppM ``Preorder #[auxiliaryType]
    let preorder ← synthInstance preorderType
    let preorder ← zetaReduce preorder
    for binding in binders do
      if ← Morew.Elab.Affine.depends binding preorder then
        throwErrorAt selector "the selected order instance depends on a decision variable"
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
    -- Imported generic sources can leave assigned universe and instance
    -- metavariables in section-local declaration types.
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionVars
    let some binderName := allocation.findName? 0
      | throwError "missing occurrence auxiliary name"
    let some boundName := allocation.findName? 1
      | throwError "missing occurrence bound name"
    let binderName ← withFreshMacroScope do MonadQuotation.addMacroScope binderName
    let selected ← selectOccurrence state typed.presentation selector row? binderName boundName direction
    -- Keep dependent model definitions intact even when prior substitution
    -- normalized the canonical problem using proved identities. Selection
    -- and context extraction use the retained presentation; this checked
    -- bridge connects it to the current semantic problem.
    let source ← if state.view.definitions.isEmpty then pure typed.canonical else do
      let sourceSyntax ← liftMacroM state.view.toTermSyntax
      elabTermEnsuringType sourceSyntax (← inferType typed.canonical)
    synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let sourceEquivalence ← if ← isDefEq typed.canonical source then
        mkAppM ``Morew.GlobalEquivalence.refl #[typed.canonical]
      else do
        let normalization ← checkedPointwiseNormalization state.sourceName
          typed.canonical source state.normalizationLemmas
        pure normalization.equivalence
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
    let equivalence ← if let some decomposition := decomposition? then
        mkAppM ``Morew.constraintBoundAtEquivalence
          #[source, decomposition, selected.selected, selected.context, direction, contextProof]
      else
        mkAppM ``Morew.objectiveBoundAtEquivalence
          #[source, selected.selected, selected.context, direction, contextProof]
    let naturalType ← whnf (← inferType equivalence)
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
    let normalization ← mkAppM ``Morew.pointwiseEquivalence
      #[natural, target, objectiveEquality, ← proveRearrangement feasibleType]
    let equivalence ← mkAppM ``Morew.GlobalEquivalence.trans #[equivalence, normalization]
    let equivalence ← mkAppM ``Morew.GlobalEquivalence.trans
      #[sourceEquivalence, equivalence]
    let equivalence ← mkAppM ``Morew.GlobalEquivalence.trans
      #[typed.normalization.equivalence, equivalence]
    let primitive ← state.runner.liftEquivalence equivalence
    let primitive ← instantiateMVars primitive
    checkWithKernel primitive
    -- Keep the checked certificate behind a constant so chained lifts do not
    -- repeatedly elaborate its expanded proof. Section parameters are retained,
    -- and the enclosing command transaction rolls it back if a later step fails.
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
      removedConstraintNames := {}
      normalizationLemmas := state.normalizationLemmas
      checkpoint? := some { semantic, view := selected.view }
    }

/-- Plan a checked bound lift at one objective or constraint occurrence. -/
def prepareOccurrenceBound (state : ReformState) (step : Syntax)
    (binder : TSyntax `ident) (selector : TSyntax `boundOccurrence)
    (constraint? explicitLabel? : Option (TSyntax `ident))
    (provided? : Option (TSyntax `term)) (direction : Morew.BoundDirection) :
    CommandElabM SurfaceStepDraft := do
  let row? ← constraint?.mapM fun label => do
    let some index := state.view.constraints.findIdx? (sameUserName ·.name label.getId)
      | throwErrorAt label "unknown or stale constraint label `{label.getId.eraseMacroScopes}`"
    pure index
  if row?.isNone then
    let expected := if direction == .upper then .minimize else .maximize
    unless state.view.sense == expected do
      throwErrorAt step "the occurrence bound has the wrong objective sense"
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

end Morew.Reformulation.Internal
