import PTran.Reformulation.State
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lean.Meta.Tactic.Simp.Main

/-!
# Surface reformulation presentations

Expression stabilization, canonical presentations, and checked normalization.
These helpers are shared by step implementations and command emission.
-/

namespace PTran.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

private def annotatedConstName? (infos : SubExpr.PosMap Elab.Info)
    (stx : Lean.Syntax) : Option Name := do
  let .ident (.synthetic start _ _) _ _ _ := stx | none
  match infos.get? start.byteIdx with
  | some (.ofTermInfo info) =>
      let .const name _ := info.expr | none
      some name
  | some (.ofDelabTermInfo info) =>
      let .const name _ := info.toTermInfo.expr | none
      some name
  | _ => none

private partial def freezeConstantReferences (infos : SubExpr.PosMap Elab.Info)
    (stx : Lean.Syntax) : Lean.Syntax :=
  if let some name := annotatedConstName? infos stx then
    mkCIdentFrom stx name
  else
    stx.setArgs <| stx.getArgs.map fun child => freezeConstantReferences infos child

private def stabilizeExpressionSyntax (expression : Expr) : TermElabM (TSyntax `term) :=
  withOptions (fun options =>
      options.set `pp.fullNames true |>.set `pp.privateNames true
        |>.set `pp.proofs true |>.set `pp.tagAppFns true
        |>.set `pp.fieldNotation false) do
    let (stable, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    pure ⟨freezeConstantReferences infos stable.raw⟩

/-- Delaborate an expression with explicit arguments and fixed constant references. -/
def exactExpressionSyntax (expression : Expr) : TermElabM (TSyntax `term) :=
  withOptions (fun options => options.set `pp.all true) do
    let (stable, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    pure ⟨freezeConstantReferences infos stable.raw⟩

/-- Elaborate and stabilize a term for reuse in generated declarations. -/
def stabilizeTerm (term : TSyntax `term) : CommandElabM (TSyntax `term) :=
  runTermElabM fun _ => do
    let expression ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasMVar then
      throwErrorAt term "term contains unresolved metavariables"
    stabilizeExpressionSyntax expression

/-- Stable type syntax for the semantic and displayed problem types. -/
structure ProblemTypeSyntax where
  /-- Stable semantic decision-domain type. -/
  domain : TSyntax `term
  /-- Stable semantic objective-value type. -/
  value : TSyntax `term
  /-- Objective-value type syntax for the displayed presentation. -/
  presentationValue : Lean.Syntax

/-- Recover stable domain and objective-value type syntax from a problem. -/
def problemTypeSyntax (optimizationProblem : TSyntax `term) :
    CommandElabM ProblemTypeSyntax :=
  runTermElabM fun _ => do
    let expression ← elabTerm optimizationProblem none
    synthesizeSyntheticMVarsNoPostponing
    let type ← whnf (← inferType (← instantiateMVars expression))
    unless type.getAppFn.isConstOf ``PTran.Problem &&
        type.getAppNumArgs == 2 do
      throwErrorAt optimizationProblem "term does not have type `PTran.Problem _ _`"
    let domain := type.getAppArgs[0]!
    let value ← whnf type.getAppArgs[1]!
    pure {
      domain := ← exactExpressionSyntax domain
      value := ← exactExpressionSyntax value
      presentationValue := (← stabilizeExpressionSyntax value).raw
    }

/-- Simplify an expression using only the supplied declarations and reductions. -/
def simpOnly (expression : Expr) (lemmas : Array Name := #[])
    (unfold : Array Name := #[]) : MetaM Expr := do
  let mut theorems : SimpTheorems := {}
  for declaration in lemmas do
    theorems ← theorems.addConst declaration
  for declaration in unfold do
    theorems ← theorems.addDeclToUnfold declaration
  let context ← Simp.mkContext
    (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← simp expression context
  instantiateMVars result.expr

private partial def splitConstraintBody (body : Expr) : Nat → MetaM (Array Expr)
  | 0 => do
      unless ← isDefEq body (mkConst ``True) do
        throwError "problem presentation metadata does not match the source feasibility predicate"
      pure #[]
  | 1 => pure #[body]
  | count + 2 => do
      let body ← whnf body
      let arguments := body.getAppArgs
      unless body.getAppFn.isConstOf ``And && arguments.size == 2 do
        throwError "problem presentation metadata does not match the source constraint structure"
      let rest ← splitConstraintBody arguments[1]! (count + 1)
      pure <| #[arguments[0]!] ++ rest

private def sourceProblemParts (sourceName : Name) (source : Expr)
    (constraintCount : Nat) : MetaM
    (Expr × Expr × Array Expr) := do
  let sourceType ← whnf (← inferType source)
  unless sourceType.getAppFn.isConstOf ``PTran.Problem &&
      sourceType.getAppNumArgs == 2 do
    throwError "reformulation source does not have type `PTran.Problem _ _`"
  let domain := sourceType.getArg! 0
  let objective ← mkAppM ``PTran.Problem.objective #[source]
  let feasible ← mkAppM ``PTran.Problem.feasible #[source]
  let constraints ← withLocalDeclD `point domain fun point => do
    let body ← simpOnly (mkApp feasible point) (unfold := #[sourceName])
    let bodies ← splitConstraintBody body constraintCount
    bodies.mapM fun body => mkLambdaFVars #[point] body
  pure (domain, objective, constraints)

private def mkConstraintConjunctionExpr : List Expr → Expr
  | [] => mkConst ``True
  | [proposition] => proposition
  | proposition :: rest =>
      mkApp2 (mkConst ``And) proposition (mkConstraintConjunctionExpr rest)

/-- Build a feasibility predicate from ordered constraint predicates. -/
def mkFeasibleFunction (domain : Expr) (constraints : Array Expr) : MetaM Expr :=
  withLocalDeclD `point domain fun point => do
    let propositions := constraints.map fun constraint => mkApp constraint point
    mkLambdaFVars #[point] <| mkConstraintConjunctionExpr propositions.toList

/-- Construct the canonical target while preserving checked source semantics. -/
def canonicalTargetExpression (sourceName : Name)
    (sourceTerm : TSyntax `term) (sourceView : PTran.Syntax.ProblemView)
    (removedConstraintNames : NameSet) (semantic : TSyntax `term)
    (simplifyExpLogTerms : Bool) : TermElabM Expr := do
  let source ← elabTerm sourceTerm none
  synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let (domain, objective, constraints) ←
    sourceProblemParts sourceName source sourceView.constraints.size
  let objectiveType ← inferType objective
  let mut constraintTypes : Array Expr := #[]
  for constraint in constraints do
    constraintTypes := constraintTypes.push (← inferType constraint)

  let rec /-- Protect source parts during reduction. -/
      withProtectedParts (types : List Expr) (protectedParts : Array Expr) :
      TermElabM Expr := do
    match types with
    | [] =>
      let protectedObjective := protectedParts[0]!
      let protectedConstraints := protectedParts.extract 1 protectedParts.size
      let protectedFeasible ←
        mkFeasibleFunction domain protectedConstraints
      let protectedSource ← mkAppM ``PTran.Problem.mk
        #[protectedObjective, protectedFeasible]
      let semanticExpression ← elabTerm semantic none
      synthesizeSyntheticMVarsNoPostponing
      let semanticExpression ← instantiateMVars semanticExpression
      let protectedSemantic := semanticExpression.replace fun expression =>
        if expression.getAppFn.isConstOf sourceName then some protectedSource else none
      let transformed ← simpOnly protectedSemantic (unfold :=
        #[``PTran.Problem.pullback, ``PTran.Problem.epigraph,
          ``PTran.Problem.hypograph])

      let exactParts := #[objective] ++ constraints
      let protectAction : StateT (Array (MVarId × Expr)) TermElabM Expr :=
        Meta.transform transformed (post := fun expression => do
          let function := expression.getAppFn
          let some partIndex := protectedParts.findIdx? fun part => part == function
            | pure (.done expression)
          let arguments := expression.getAppArgs
          if arguments.isEmpty then
            pure (.done expression)
          else
            let exact := mkAppN exactParts[partIndex]! arguments
            let exact ← simpOnly exact
              (if simplifyExpLogTerms then #[``Real.log_exp, ``Real.exp_pos] else #[])
              (unfold := #[sourceName])
            let removedSourceConstraint := partIndex > 0 &&
              removedConstraintNames.contains
                sourceView.constraints[partIndex - 1]!.name.eraseMacroScopes
            if removedSourceConstraint then
              -- The step supplied checked normalization evidence for this
              -- removal.  Use the canonical `True` row here even when the
              -- source predicate reaches positivity through a reducible
              -- alias; the normalization proof below remains the soundness
              -- check against the natural semantic problem.
              pure (.done (mkConst ``True))
            else
              let placeholder ← mkFreshExprMVar (some (← inferType exact))
                (kind := .syntheticOpaque)
              modify fun assignments =>
                assignments.push (placeholder.mvarId!, exact)
              pure (.done placeholder))
      let (transformedProtected, assignments) ← protectAction.run #[]
      let normalized ← simpOnly transformedProtected
        #[``true_and, ``and_true, ``and_assoc]
      let closed ← mkLambdaFVars protectedParts normalized
      let result := mkAppN closed exactParts
      for (placeholder, exact) in assignments do
        MVarId.assign placeholder exact
      instantiateMVars result
    | type :: rest =>
      let name := if protectedParts.isEmpty then `objective else `constraint
      withLocalDeclD name type fun part =>
        withProtectedParts rest (protectedParts.push part)

  withProtectedParts (objectiveType :: constraintTypes.toList) #[]

private partial def splitProductDomain (domain : Expr) : Nat → MetaM (Array Expr)
  | 0 => throwError "a problem presentation requires at least one decision variable"
  | 1 => pure #[domain]
  | count + 2 => do
      let domain ← whnf domain
      let arguments := domain.getAppArgs
      unless domain.getAppFn.isConstOf ``Prod && arguments.size == 2 do
        throwError "problem presentation binder structure does not match the target domain"
      let initialTypes ← splitProductDomain arguments[0]! (count + 1)
      pure <| initialTypes.push arguments[1]!

/-- Pack decision coordinates into the presentation's left-associated product. -/
def packPoint (components : Array Expr) : MetaM Expr := do
  if h : components.size > 0 then
    let mut point := components[0]
    for index in [1:components.size] do
      point ← mkAppM ``Prod.mk #[point, components[index]!]
    pure point
  else
    throwError "a problem presentation requires at least one decision variable"

private def annotatedFVarId? (infos : SubExpr.PosMap Elab.Info)
    (stx : Lean.Syntax) : Option FVarId := do
  let .ident (.synthetic start _ _) _ _ _ := stx | none
  match infos.get? start.byteIdx with
  | some (.ofTermInfo info) =>
      let .fvar id := info.expr | none
      some id
  | some (.ofDelabTermInfo info) =>
      let .fvar id := info.toTermInfo.expr | none
      some id
  | _ => none

private partial def freezePresentationReferences
    (infos : SubExpr.PosMap Elab.Info) (binders : Array (FVarId × Name))
    (stx : Lean.Syntax) : Lean.Syntax :=
  if let some id := annotatedFVarId? infos stx then
    match binders.find? fun entry => entry.1 == id with
    | some (_, name) => mkIdentFrom stx name
    | none => stx
  else if let some name := annotatedConstName? infos stx then
    mkCIdentFrom stx name
  else
    stx.setArgs <| stx.getArgs.map fun child =>
      freezePresentationReferences infos binders child

private def delabPresentationTerm (expression : Expr)
    (binders : Array (FVarId × Name)) : TermElabM Lean.Syntax := do
  let (stx, infos) ← PrettyPrinter.delabCore expression {}
    PrettyPrinter.Delaborator.delab
  pure <| freezePresentationReferences infos binders stx.raw

private def problemViewFromExpression (target : Expr)
    (template : PTran.Syntax.ProblemView) : TermElabM PTran.Syntax.ProblemView := do
  let targetType ← whnf (← inferType target)
  unless targetType.getAppFn.isConstOf ``PTran.Problem &&
      targetType.getAppNumArgs == 2 do
    throwError "reformulation target does not have type `PTran.Problem _ _`"
  let domain := targetType.getArg! 0
  let binderTypes ← splitProductDomain domain template.binders.size
  let binderDeclarations := binderTypes.mapIdx fun index type =>
    (template.binders[index]!.name, type)
  withLocalDeclsDND binderDeclarations fun binders => do
    let point ← packPoint binders
    let objective ← mkAppM ``PTran.Problem.objective #[target]
    let objectiveBody ← simpOnly (mkApp objective point)
    let feasible ← mkAppM ``PTran.Problem.feasible #[target]
    let feasibleBody ← simpOnly (mkApp feasible point)
    let constraints ← splitConstraintBody feasibleBody template.constraints.size
    let binderNames := binders.mapIdx fun index binder =>
      (binder.fvarId!, template.binders[index]!.name)
    let objectiveSyntax ← delabPresentationTerm objectiveBody binderNames
    let constraintSyntax ← constraints.mapM fun proposition =>
      delabPresentationTerm proposition binderNames
    pure {
      template with
      objective := objectiveSyntax
      constraints := template.constraints.mapIdx fun index constraint =>
        { constraint with proposition := constraintSyntax[index]! }
    }

/-- Recover a typed presentation from a checked problem expression. -/
def typedPresentationFromExpression (target : Expr)
    (template : PTran.Syntax.ProblemView) :
    TermElabM PTran.Elab.Reformulation.PresentationState := do
  let targetType ← whnf (← inferType target)
  unless targetType.getAppFn.isConstOf ``PTran.Problem &&
      targetType.getAppNumArgs == 2 do
    throwError "reformulation presentation target is not a `PTran.Problem`"
  let domain := targetType.getAppArgs[0]!
  let value := targetType.getAppArgs[1]!
  let binderTypes ← splitProductDomain domain template.binders.size
  let objective ← mkAppM ``PTran.Problem.objective #[target]
  let feasible ← mkAppM ``PTran.Problem.feasible #[target]
  let constraintPredicates ← withLocalDeclD `point domain fun point => do
    let feasibleBody ← simpOnly (mkApp feasible point)
    let bodies ← splitConstraintBody feasibleBody template.constraints.size
    bodies.mapM fun body => mkLambdaFVars #[point] body
  pure {
    sense := template.sense
    domainType := domain
    valueType := value
    binders := template.binders.mapIdx fun index binder => {
      name := binder.name
      type := binderTypes[index]!
    }
    objective
    constraints := template.constraints.mapIdx fun index constraint => {
      name := constraint.name
      predicate := constraintPredicates[index]!
    }
  }

/-- Register a presentation recovered from an emitted target declaration. -/
def refreshProblemView (targetName : Name)
    (template : PTran.Syntax.ProblemView) : CommandElabM Unit := do
  let refreshed ← runTermElabM fun _ => do
    let targetSyntax : TSyntax `term :=
      ⟨mkIdent (`_root_ ++ targetName)⟩
    let target ← elabTerm targetSyntax none
    synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars target
    let some target ← unfoldDefinition? target
      | throwError "cannot inspect reformulation target `{targetName}`"
    problemViewFromExpression target template
  PTran.Syntax.registerProblemView targetName refreshed

/-- Rebase a retained presentation into the current section-variable context. -/
def withTypedPresentation (state : ReformState)
    (action : PTran.Elab.Reformulation.PresentationState → TermElabM α) :
    CommandElabM α :=
  runTermElabM fun sectionFVars =>
    action <| state.typed.presentation.replaceFVars state.sectionFVars sectionFVars

/-- Run an elaboration action under the presentation's typed decision binders. -/
def withPresentationBinders [Inhabited α]
    (presentation : PTran.Elab.Reformulation.PresentationState)
    (action : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let binderTypes := presentation.binders.map (·.type)
  let declarations := binderTypes.mapIdx fun index type =>
    (presentation.binders[index]!.name, type)
  withLocalDeclsDND declarations fun binders => action binderTypes binders

/-- Build the shared simplification set for accumulated normalization evidence. -/
def normalizationSimpLemmas (sourceTerm : TSyntax `term)
    (predicateLemmas : Array (TSyntax `term)) :
    MacroM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let sourceLemma ← `(
    Lean.Parser.Tactic.simpLemma| $sourceTerm:term)
  let mut lemmas := #[sourceLemma]
  for proof in predicateLemmas do
    lemmas := lemmas.push (← `(
      Lean.Parser.Tactic.simpLemma| $proof:term))
  for declaration in #[``PTran.Problem.pullback, ``PTran.Problem.epigraph,
      ``PTran.Problem.hypograph, ``Real.log_exp, ``Real.exp_pos,
      ``true_and, ``and_true, ``and_assoc, ``eq_self, ``iff_self] do
    lemmas := lemmas.push (← `(
      Lean.Parser.Tactic.simpLemma| $(mkIdent declaration):term))
  pure lemmas

/-- Construct and check normalization from semantic to canonical problems. -/
def checkedPointwiseNormalization (sourceTerm : TSyntax `term)
    (semantic canonical : Expr) (predicateLemmas : Array (TSyntax `term)) :
    TermElabM PTran.Elab.Reformulation.PointwiseNormalization := do
  let semanticType ← whnf (← inferType semantic)
  let canonicalType ← whnf (← inferType canonical)
  unless semanticType.getAppFn.isConstOf ``PTran.Problem &&
      semanticType.getAppNumArgs == 2 &&
      canonicalType.getAppFn.isConstOf ``PTran.Problem &&
      canonicalType.getAppNumArgs == 2 do
    throwError "pointwise normalization requires two optimization problems"
  let domain := semanticType.getAppArgs[0]!
  unless ← isDefEq domain canonicalType.getAppArgs[0]! do
    throwError "pointwise normalization changed the decision domain"
  unless ← isDefEq semanticType.getAppArgs[1]! canonicalType.getAppArgs[1]! do
    throwError "pointwise normalization changed the objective value type"
  let semanticObjective ← mkAppM ``PTran.Problem.objective #[semantic]
  let canonicalObjective ← mkAppM ``PTran.Problem.objective #[canonical]
  let semanticFeasible ← mkAppM ``PTran.Problem.feasible #[semantic]
  let canonicalFeasible ← mkAppM ``PTran.Problem.feasible #[canonical]
  let objectiveType ← withLocalDeclD `point domain fun point => do
    let equality ← mkEq (mkApp semanticObjective point)
      (mkApp canonicalObjective point)
    mkForallFVars #[point] equality
  let feasibleType ← withLocalDeclD `point domain fun point => do
    mkForallFVars #[point] <| mkApp2 (mkConst ``Iff)
      (mkApp semanticFeasible point) (mkApp canonicalFeasible point)
  let simpLemmas ← liftMacroM <|
    normalizationSimpLemmas sourceTerm predicateLemmas
  let proofSyntax ← liftMacroM `(
    fun _ => by
      simp only [$[$simpLemmas],*] <;> rfl)
  let objectiveEquality ← elabTerm proofSyntax (some objectiveType)
  synthesizeSyntheticMVarsNoPostponing
  let objectiveEquality ← instantiateMVars objectiveEquality
  let feasibleIff ← elabTerm proofSyntax (some feasibleType)
  synthesizeSyntheticMVarsNoPostponing
  let feasibleIff ← instantiateMVars feasibleIff
  let equivalence ← mkAppM ``PTran.pointwiseEquivalence
    #[semantic, canonical, objectiveEquality, feasibleIff]
  let normalization : PTran.Elab.Reformulation.PointwiseNormalization := {
    semantic
    canonical
    objectiveEquality
    feasibleIff
    equivalence
  }
  normalization.check
  pure normalization

/-- Describe the checked binder, objective, and constraint presentation changes. -/
def presentationDeltaBetween
    (current next : PTran.Elab.Reformulation.PresentationState)
    (objectiveEquality feasibleIff : Expr) :
    MetaM PTran.Elab.Reformulation.PresentationDelta := do
  if next.binders.size < current.binders.size then
    throwError "reformulation steps cannot remove decision-variable binders"
  let mut binderReplacements := #[]
  for index in [:current.binders.size] do
    let oldBinder := current.binders[index]!
    let newBinder := next.binders[index]!
    unless ← isDefEq oldBinder.type newBinder.type do
      throwError "reformulation changed the type of decision variable `{oldBinder.name}`"
    unless sameUserName oldBinder.name newBinder.name do
      let typeEquality ← mkEqRefl oldBinder.type
      binderReplacements := binderReplacements.push {
        index
        entry := newBinder
        typeEquality
      }
  let mut binderAdditions := #[]
  for index in [current.binders.size:next.binders.size] do
    let domainEquality ← mkEqRefl next.domainType
    binderAdditions := binderAdditions.push {
      entry := next.binders[index]!
      domainEquality
    }

  let mut constraintReplacements := #[]
  for index in [:current.constraints.size] do
    let currentConstraint := current.constraints[index]!
    let replacement := next.constraints.find? fun candidate =>
      sameUserName candidate.name currentConstraint.name
    constraintReplacements := constraintReplacements.push {
      index
      entries := replacement.toArray
      pointwiseIff := feasibleIff
    }
  let mut constraintAdditions := #[]
  for constraint in next.constraints do
    unless current.constraints.any fun candidate =>
        sameUserName candidate.name constraint.name do
      constraintAdditions := constraintAdditions.push {
        entry := constraint
        pointwiseIff := feasibleIff
      }
  pure {
    domainType? := some next.domainType
    valueType? := some next.valueType
    binderReplacements
    binderAdditions
    objective? := some {
      objective := next.objective
      pointwiseEquality := objectiveEquality
    }
    constraintReplacements
    constraintAdditions
    normalizationObjectiveEquality? := some objectiveEquality
    normalizationFeasibleIff? := some feasibleIff
  }

end PTran.Reformulation.Internal
