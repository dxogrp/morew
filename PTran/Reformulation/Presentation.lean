import PTran.Reformulation.State
import PTran.Conic.SecondOrder
import PTran.Conic.Exponential.Cone
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

/-- Retain readable spelling while fixing the declaration and preventing local
capture, just as `mkCIdentFrom` does for fully qualified identifiers. -/
private def freezePresentationConstant (stx : Lean.Syntax) (name : Name) : Lean.Syntax :=
  match (mkCIdentFrom stx stx.getId).raw with
  | .ident info raw identifier _ => .ident info raw identifier [.decl name []]
  | _ => mkCIdentFrom stx name

private partial def freezePresentationReferences
    (infos : SubExpr.PosMap Elab.Info) (binders : Array (FVarId × Name))
    (stx : Lean.Syntax) : Lean.Syntax :=
  if let some id := annotatedFVarId? infos stx then
    match binders.find? fun entry => entry.1 == id with
    | some (_, name) => mkIdentFrom stx name
    -- Presentation syntax is persisted and may be used in another section.
    -- Keep local names instead of capturing the current section's UIDs.
    | none => stx
  else if let some name := annotatedConstName? infos stx then
    freezePresentationConstant stx name
  else
    stx.setArgs <| stx.getArgs.map fun child =>
      freezePresentationReferences infos binders child

/-- Section variable UIDs survive fresh elaboration contexts, including for
anonymous instances whose local names receive new macro scopes each time.
They are suitable for transient semantic syntax within the current section. -/
private def sectionReferenceNames : TermElabM (Std.HashMap FVarId Name) := do
  let mut references := {}
  for (uid, sectionVar) in (← read).sectionFVars do
    if let .fvar id := sectionVar then
      references := references.insert id uid
  pure references

private partial def freezeConstantReferences (infos : SubExpr.PosMap Elab.Info)
    (sectionReferences : Std.HashMap FVarId Name)
    (stx : Lean.Syntax) : Lean.Syntax :=
  if let some uid := (annotatedFVarId? infos stx).bind sectionReferences.get? then
    mkCIdentFrom stx uid
  else if let some name := annotatedConstName? infos stx then
    mkCIdentFrom stx name
  else
    stx.setArgs <| stx.getArgs.map fun child =>
      freezeConstantReferences infos sectionReferences child

private def stabilizeExpressionSyntax (expression : Expr) : TermElabM (TSyntax `term) :=
  withOptions (fun options =>
      options.set `pp.fullNames true |>.set `pp.privateNames true
        |>.set `pp.explicit true |>.set `pp.instances true
        |>.set `pp.proofs true |>.set `pp.tagAppFns true
        |>.set `pp.deepTerms true |>.set `pp.structureInstanceTypes true
        |>.set `pp.funBinderTypes true
        |>.set `pp.numericTypes true
        |>.set `pp.maxSteps (1000000 : Nat)
        |>.set `pp.fieldNotation false) do
    let (stable, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    pure ⟨freezeConstantReferences infos (← sectionReferenceNames) stable.raw⟩

/-- Delaborate an expression with explicit arguments and fixed constant references. -/
def exactExpressionSyntax (expression : Expr) : TermElabM (TSyntax `term) :=
  withOptions (fun options => options.set `pp.all true
      |>.set `pp.explicit true |>.set `pp.instances true
      |>.set `pp.proofs true |>.set `pp.deepTerms true
      |>.set `pp.structureInstances false |>.set `pp.beta true
      |>.set `pp.maxSteps (1000000 : Nat)) do
    let (stable, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    pure ⟨freezeConstantReferences infos (← sectionReferenceNames) stable.raw⟩

/-- Elaborate and stabilize a term for reuse in generated declarations. -/
def stabilizeTerm (term : TSyntax `term) : CommandElabM (TSyntax `term) :=
  runTermElabM fun _ => do
    let expression ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasMVar then
      throwErrorAt term "term contains unresolved metavariables"
    stabilizeExpressionSyntax expression

/-- Readable binder type syntax with fixed global references and local names
that can be retained in presentation metadata across sections. -/
def presentationTypeSyntax (type : Expr) : TermElabM Lean.Syntax :=
  -- Generated auxiliary types need the same fixed class projections as row
  -- bodies, while retaining their readable spelling in imported metadata.
  withOptions (fun options => options.setBool `pp.tagAppFns true) do
    let (stx, infos) ← PrettyPrinter.delabCore type {}
      PrettyPrinter.Delaborator.delab
    pure <| freezePresentationReferences infos #[] stx.raw

/-- Stable type syntax for the semantic and displayed problem types. -/
structure ProblemTypeSyntax where
  /-- Stable semantic decision-domain type. -/
  domain : TSyntax `term
  /-- Stable semantic objective-value type. -/
  value : TSyntax `term
  /-- Objective-value type syntax for the displayed presentation. -/
  presentationValue : Lean.Syntax

/-- Recover stable type syntax directly from an already checked problem. -/
def problemTypeSyntaxFromExpression (expression : Expr) :
    TermElabM ProblemTypeSyntax := do
  let type ← whnf (← inferType expression)
  unless type.getAppFn.isConstOf ``PTran.Problem &&
      type.getAppNumArgs == 2 do
    throwError "term does not have type `PTran.Problem _ _`"
  let domain := type.getAppArgs[0]!
  let value := type.getAppArgs[1]!
  pure {
    domain := ← exactExpressionSyntax domain
    value := ← exactExpressionSyntax value
    presentationValue := ← presentationTypeSyntax (← whnf value)
  }

/-- Recover stable domain and objective-value type syntax from a problem. -/
def problemTypeSyntax (optimizationProblem : TSyntax `term) :
    CommandElabM ProblemTypeSyntax :=
  runTermElabM fun _ => withRef optimizationProblem do
    let expression ← elabTerm optimizationProblem none
    synthesizeSyntheticMVarsNoPostponing
    problemTypeSyntaxFromExpression (← instantiateMVars expression)

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

/-- Replace only the checkpoint at the base of the supported transformation
spine. In particular, do not search inside user objectives or constraints for
references to an original source declaration. -/
private partial def protectCheckpoint (expression checkpoint replacement : Expr) : MetaM Expr := do
  let expression := expression.consumeMData.headBeta
  if expression == checkpoint then return replacement
  if let .letE _ _ value body _ := expression then
    return ← protectCheckpoint (body.instantiate1 value) checkpoint replacement
  let arguments := expression.getAppArgs
  let isPullback := expression.isAppOfArity ``PTran.Problem.pullback 5
  let isBound := expression.isAppOfArity ``PTran.Problem.epigraph 4 ||
    expression.isAppOfArity ``PTran.Problem.hypograph 4
  unless isPullback || isBound do
    if ← isDefEq expression checkpoint then return replacement
    throwError "reformulation semantic problem does not extend its canonicalization checkpoint"
  let base ← protectCheckpoint arguments[3]! checkpoint replacement
  pure <| mkAppN expression.getAppFn (arguments.set! 3 base)

/-- Construct the canonical target while protecting the checkpoint's ordered
rows. `sourceName` is retained only for unfolding the original problem container;
the checkpoint itself may be an explicitly constructed canonical problem. -/
def canonicalTargetExpressionFromExpressions (sourceName : Name)
    (source : Expr) (sourceView : PTran.Syntax.ProblemView)
    (removedConstraintNames : NameSet) (semanticExpression : Expr)
    (simplifyExpLogTerms : Bool) : TermElabM Expr := do
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
      let protectedSemantic ← protectCheckpoint semanticExpression source protectedSource
      let transformed ← simpOnly protectedSemantic (unfold :=
        #[``PTran.Problem.pullback, ``PTran.Problem.epigraph,
          ``PTran.Problem.hypograph])

      -- A same-domain rewrite can leave the protected objective as a bare
      -- function. Normalize that function before restoring it, as well as
      -- normalizing its applications below.
      let exactObjective ← simpOnly objective (unfold := #[sourceName])
      let exactParts := #[exactObjective] ++ constraints
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

/-- Elaborate a source and transformation spine, then canonicalize their checked
expressions while protecting the checkpoint's ordered rows. -/
def canonicalTargetExpression (sourceName : Name)
    (sourceTerm : TSyntax `term) (sourceView : PTran.Syntax.ProblemView)
    (removedConstraintNames : NameSet) (semantic : TSyntax `term)
    (simplifyExpLogTerms : Bool) : TermElabM Expr := do
  let source ← elabTerm sourceTerm none
  synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let semanticExpression ← elabTerm semantic none
  synthesizeSyntheticMVarsNoPostponing
  let semanticExpression ← instantiateMVars semanticExpression
  canonicalTargetExpressionFromExpressions sourceName source sourceView
    removedConstraintNames semanticExpression simplifyExpLogTerms

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

/-- Internal delaboration flag, enabled only while generating stored presentations.
Keeping it unregistered prevents ordinary pretty-printing options from enabling it. -/
private def coneNotationOption : Name := `PTran.Reformulation.Internal.coneNotation

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.PTran.Conic.Cone.carrier]
private def delabConeCarrier : Delab := do
  unless (← getOptions).getBool coneNotationOption do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``PTran.Conic.Cone.carrier 1
  let cone := expression.getAppArgs[0]!
  if cone.isConstOf ``PTran.Conic.Cone.exponential then
    return ← `(EXP)
  guard <| cone.isAppOfArity ``PTran.Conic.Cone.secondOrder 1 ||
    cone.isAppOfArity ``PTran.Conic.Cone.rotatedSecondOrder 1
  -- Keep the original subexpression position, so dimension references are
  -- frozen by the same pass as the rest of the generated presentation.
  let dimension ← withAppArg <| withAppArg delab
  if cone.isAppOfArity ``PTran.Conic.Cone.secondOrder 1 then
    `(SOC $dimension)
  else
    `(RSOC $dimension)

private def delabPresentationTerm (expression : Expr)
    (binders : Array (FVarId × Name)) : TermElabM Lean.Syntax :=
  -- Tag application heads as constants even when their arguments are implicit,
  -- so dimensions and coefficients supplied by class projections stay frozen.
  withOptions (fun options => options.setBool coneNotationOption true
      |>.setBool `pp.tagAppFns true) do
    let (stx, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    pure <| freezePresentationReferences infos binders stx.raw

/-- Recover printable bodies from a checked problem while retaining the supplied
ordered names. Applied sources also instantiate binder types; existing bare-name
sources retain their original spelling, including type aliases. -/
def problemViewFromExpression (target : Expr)
    (template : PTran.Syntax.ProblemView) (instantiateBinderTypes : Bool := false) :
    TermElabM PTran.Syntax.ProblemView := do
  let targetType ← whnf (← inferType target)
  unless targetType.getAppFn.isConstOf ``PTran.Problem &&
      targetType.getAppNumArgs == 2 do
    throwError "reformulation target does not have type `PTran.Problem _ _`"
  let domain := targetType.getArg! 0
  let binderTypes ← splitProductDomain domain template.binders.size
  let displayedBinders ← template.binders.mapIdxM fun index binder => do
    if instantiateBinderTypes then
      pure { binder with typeSyntax := ← presentationTypeSyntax binderTypes[index]! }
    else
      pure binder
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
      binders := displayedBinders
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
    (template : PTran.Syntax.ProblemView) (instantiateBinderTypes : Bool := false) :
    CommandElabM Unit := do
  let refreshed ← runTermElabM fun _ => do
    -- Inspect the declaration's own parameters, independently of the section
    -- that emitted it. Fresh universe metavariables or ambient local names
    -- must not leak into persistent presentation metadata.
    let info ← getConstInfo targetName
    let target := Lean.mkConst targetName (info.levelParams.map Level.param)
    withLCtx {} {} do
      forallTelescopeReducing info.type (fun parameters _ => do
        let target := mkAppN target parameters
        let some target ← unfoldDefinition? target
          | throwError "cannot inspect reformulation target `{targetName}`"
        problemViewFromExpression target template instantiateBinderTypes)
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
def normalizationSimpLemmas (sourceName : Name)
    (predicateLemmas : Array (TSyntax `term)) :
    MacroM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let sourceTerm := mkCIdent sourceName
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
def checkedPointwiseNormalization (sourceName : Name)
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
    normalizationSimpLemmas sourceName predicateLemmas
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
    (objectiveEquality feasibleIff : Expr)
    (constraintSplices : Array ConstraintSplice := #[]) :
    MetaM PTran.Elab.Reformulation.PresentationDelta := do
  let mut selected : Array Nat := #[]
  for splice in constraintSplices do
    unless splice.index < current.constraints.size do
      throwError "constraint splice index is out of bounds"
    if selected.contains splice.index then
      throwError "duplicate constraint splice index"
    selected := selected.push splice.index
  let mut ranges : Array (Nat × Nat) := #[]
  unless constraintSplices.isEmpty do
    let mut offset := 0
    for index in [:current.constraints.size] do
      let splice? := constraintSplices.find? (·.index == index)
      let count := splice?.map (·.count) |>.getD 1
      unless offset + count ≤ next.constraints.size do
        throwError "constraint splice does not match the next presentation shape"
      if splice?.isNone then
        unless sameUserName current.constraints[index]!.name next.constraints[offset]!.name do
          throwError "constraint splice changed the order of an unselected constraint"
      ranges := ranges.push (offset, count)
      offset := offset + count
    unless offset == next.constraints.size do
      throwError "constraint splice does not match the next presentation shape"
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
    unless constraintSplices.isEmpty do
      let (offset, count) := ranges[index]!
      constraintReplacements := constraintReplacements.push {
        index
        entries := next.constraints.extract offset (offset + count)
        pointwiseIff := feasibleIff
      }
      continue
    let currentConstraint := current.constraints[index]!
    let replacement := next.constraints.find? fun candidate =>
      sameUserName candidate.name currentConstraint.name
    constraintReplacements := constraintReplacements.push {
      index
      entries := replacement.toArray
      pointwiseIff := feasibleIff
    }
  let mut constraintAdditions := #[]
  for index in [:next.constraints.size] do
    unless constraintSplices.isEmpty do continue
    let constraint := next.constraints[index]!
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
