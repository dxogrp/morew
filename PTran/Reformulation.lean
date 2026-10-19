import PTran.Elab.Reformulation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lean.Elab.MutualDef
import Lean.Meta.Tactic.Simp.Main

/-!
# Reformulation command

This module implements the small, proof-producing transformation language used
by PTran's first release.  A reformulation command declares both the transformed
problem and a `GlobalEquivalence` certificate.  Convexity is deliberately not
part of either the command or the generated proof.
-/

namespace PTran

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

/-- Syntax category for one proof-producing reformulation step. -/
declare_syntax_cat reformulationStep

/-- Substitute a decision variable with a parameterization, optionally using
an explicit feasible-surjection certificate. -/
syntax (name := substituteStep)
  "substitute " ident " := " term (" using " term)? : reformulationStep
/-- Introduce an epigraph variable for a minimization objective, optionally
choosing the generated constraint's presentation label. -/
syntax (name := epigraphStep)
  "epigraph " ident (" as " ident)? : reformulationStep
/-- Introduce a hypograph variable for a maximization objective, optionally
choosing the generated constraint's presentation label. -/
syntax (name := hypographStep)
  "hypograph " ident (" as " ident)? : reformulationStep

/-- Declare a transformed problem together with its global-equivalence
certificate. -/
syntax (name := reformulationCmd)
  "reformulation" ident ":" ident ("certificate" ident)? ":=" "by" ppLine
    ppIndent(reformulationStep*) : command

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

private def sameUserName (a b : Name) : Bool :=
  a.eraseMacroScopes == b.eraseMacroScopes

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

private partial def mkConstraintConjunctionSyntax :
    List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `(True)
  | [proposition] => pure proposition
  | proposition :: rest => do
      let tail ← mkConstraintConjunctionSyntax rest
      `($proposition ∧ $tail)

private partial def collectIdents (stx : Lean.Syntax) (result : NameSet := {}) : NameSet :=
  match stx with
  | .ident _ _ value preResolved =>
      if preResolved.any fun
          | .decl _ _ => true
          | _ => false then
        result
      else
        result.insert value.eraseMacroScopes
  | _ => stx.getArgs.foldl (fun result child => collectIdents child result) result

private def newBinderCandidates (view : PTran.Syntax.ProblemView) (oldName : Name)
    (replacement : Lean.Syntax) : CommandElabM (Array Name) := do
  let localNames : NameSet := view.binders.foldl
    (fun names binder => names.insert binder.name.eraseMacroScopes) ({} : NameSet)
  let env ← getEnv
  let candidates := (collectIdents replacement).toList.filter fun name =>
    !name.isAnonymous && !sameUserName name oldName &&
      !localNames.contains name && !env.contains name
  pure candidates.toArray

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

private def exactExpressionSyntax (expression : Expr) : TermElabM (TSyntax `term) :=
  withOptions (fun options => options.set `pp.all true) do
    let (stable, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    pure ⟨freezeConstantReferences infos stable.raw⟩

private def stabilizeTerm (term : TSyntax `term) : CommandElabM (TSyntax `term) :=
  runTermElabM fun _ => do
    let expression ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    if expression.hasMVar then
      throwErrorAt term "term contains unresolved metavariables"
    stabilizeExpressionSyntax expression

private structure ProblemTypeSyntax where
  domain : TSyntax `term
  value : TSyntax `term
  presentationValue : Lean.Syntax

private def problemTypeSyntax (optimizationProblem : TSyntax `term) :
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

private def simpOnly (expression : Expr) (lemmas : Array Name := #[])
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

private def mkFeasibleFunction (domain : Expr) (constraints : Array Expr) : MetaM Expr :=
  withLocalDeclD `point domain fun point => do
    let propositions := constraints.map fun constraint => mkApp constraint point
    mkLambdaFVars #[point] <| mkConstraintConjunctionExpr propositions.toList

private def canonicalTargetExpression (sourceName : Name)
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

  let rec withProtectedParts (types : List Expr) (protectedParts : Array Expr) :
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

private def packPoint (components : Array Expr) : MetaM Expr := do
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

private def typedPresentationFromExpression (target : Expr)
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

private def refreshProblemView (targetName : Name)
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

private abbrev CertificateRunner :=
  PTran.Elab.Reformulation.CertificateRunner

private def namedTerm (name : Name) : TSyntax `term :=
  ⟨mkIdent name⟩

private def certificateRelationTerm (runner : CertificateRunner)
    (source target : TSyntax `term) : MacroM (TSyntax `term) := do
  let relation := namedTerm runner.relation
  `($relation $source $target)

private def certificateReflTerm (runner : CertificateRunner)
    (optimizationProblem : TSyntax `term) : MacroM (TSyntax `term) := do
  let refl := namedTerm runner.refl
  `($refl $optimizationProblem)

private def certificateTransTerm (runner : CertificateRunner)
    (left right : TSyntax `term) : MacroM (TSyntax `term) := do
  let trans := namedTerm runner.trans
  `($trans $left $right)

private def liftCertificateEquivalence (runner : CertificateRunner)
    (proofTerm : TSyntax `term) : MacroM (TSyntax `term) := do
  match runner.liftEquivalence? with
  | none => pure proofTerm
  | some liftName =>
      let lift := namedTerm liftName
      `($lift $proofTerm)

private def globalEquivalenceRunner : CertificateRunner :=
  PTran.Elab.Reformulation.globalEquivalenceRunner

private structure ReformState where
  typed : PTran.Elab.Reformulation.RunnerState
  sectionFVars : Array Expr
  view : PTran.Syntax.ProblemView
  semantic : TSyntax `term
  semanticDomainType : TSyntax `term
  semanticValueType : TSyntax `term
  presentationValueType : Lean.Syntax
  /-- Re-elaboratable mirror of the checked typed certificate, retained only
  for command emission so section variables keep their source binders. -/
  certificateSyntax : TSyntax `term
  source : TSyntax `term
  sourceName : Name
  runner : CertificateRunner
  simplifyExpLogTerms : Bool := false
  hasSubstitution : Bool := false
  removedConstraintNames : NameSet := {}
  normalizationUnfolds : Array Name := #[]

/-- A handler describes one uncommitted primitive step.  Certificate
composition and state mutation are deliberately centralized in
`commitSurfaceStep`. -/
private structure SurfaceStepResult where
  view : PTran.Syntax.ProblemView
  semantic : TSyntax `term
  semanticDomainType : TSyntax `term
  primitiveCertificate : TSyntax `term
  simplifyExpLogTerms : Bool
  hasSubstitution : Bool
  removedConstraintNames : NameSet
  normalizationUnfolds : Array Name
  status : PTran.Elab.Reformulation.StepStatus := .continue
  companions : Array PTran.Elab.Reformulation.CompanionRequest := #[]

/-- Surface-specific preparation retained around the reusable typed plan.  Its
materializer is not run until the typed name-request batch has passed
preflight. -/
private structure SurfaceStepDraft where
  nameRequests : Array PTran.Elab.Reformulation.NameRequest
  materialize : PTran.Elab.Reformulation.NameAllocation →
    CommandElabM SurfaceStepResult

/-- The syntax needed to emit a checked typed result. -/
private structure SurfaceMaterialization where
  surface : SurfaceStepResult
  sectionFVars : Array Expr

private abbrev SurfaceMaterializerM :=
  StateT (Option SurfaceMaterialization) CommandElabM

private def findBinderIndex (view : PTran.Syntax.ProblemView) (name : Name) : Option Nat :=
  view.binders.findIdx? fun binder => sameUserName binder.name name

private def withPresentationBinders [Inhabited α] (view : PTran.Syntax.ProblemView)
    (action : Array Expr → Array Expr → TermElabM α) : TermElabM α := do
  let binderTypes ← view.binders.mapM fun binder => do
    let typeSyntax : TSyntax `term := ⟨binder.typeSyntax⟩
    let type ← elabTerm typeSyntax none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars type
  let declarations := binderTypes.mapIdx fun index type =>
    (view.binders[index]!.name, type)
  withLocalDeclsDND declarations fun binders => action binderTypes binders

private def inferNewBinder (view : PTran.Syntax.ProblemView) (oldName : Name)
    (binderIndex : Nat) (replacement : TSyntax `term) : CommandElabM Name := do
  let candidates ← newBinderCandidates view oldName replacement.raw
  if candidates.isEmpty then
    throwErrorAt replacement
      "cannot determine the new decision variable; the substitution expression must contain one new identifier"
  let usedCandidates ← runTermElabM fun _ =>
    withPresentationBinders view fun binderTypes _ => do
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

private def replacementIsRealExpOf (view : PTran.Syntax.ProblemView)
    (binderIndex : Nat) (replacement : TSyntax `term) : CommandElabM Bool :=
  runTermElabM fun _ => withPresentationBinders view fun binderTypes binders => do
    let expression ← elabTerm replacement (some binderTypes[binderIndex]!)
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    let arguments := expression.getAppArgs
    pure <| expression.getAppFn.isConstOf ``Real.exp && arguments.size == 1 &&
      arguments[0]!.fvarId? == binders[binderIndex]!.fvarId?

private structure PositiveConstraintMatch where
  index : Nat
  unfold? : Option Name

private def findPositiveConstraint (view : PTran.Syntax.ProblemView)
    (binderIndex : Nat) : CommandElabM (Option PositiveConstraintMatch) :=
  runTermElabM fun _ => withPresentationBinders view fun _ _binders => do
    let binder : TSyntax `term := ⟨mkIdent view.binders[binderIndex]!.name⟩
    let expectedSyntax ← liftMacroM `(0 < $binder)
    let expected ← elabTerm expectedSyntax (some (mkSort Level.zero))
    synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    for index in [:view.constraints.size] do
      let proposition : TSyntax `term :=
        ⟨view.constraints[index]!.proposition⟩
      let candidate ← elabTerm proposition (some (mkSort Level.zero))
      synthesizeSyntheticMVarsNoPostponing
      let candidate ← instantiateMVars candidate
      if ← isDefEq candidate expected then
        let unfold? := match candidate.getAppFn, expected.getAppFn with
          | .const candidateName _, .const expectedName _ =>
              if candidateName == expectedName then none else some candidateName
          | _, _ => none
        return some { index, unfold? }
    pure none

private def constraintIsTypedTrue (view : PTran.Syntax.ProblemView)
    (index : Nat) : CommandElabM Bool :=
  runTermElabM fun _ => withPresentationBinders view fun _ _ => do
    let proposition : TSyntax `term := ⟨view.constraints[index]!.proposition⟩
    let expression ← elabTerm proposition (some (mkSort Level.zero))
    synthesizeSyntheticMVarsNoPostponing
    let expression ← instantiateMVars expression
    isDefEq expression (mkConst ``True)

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
  let renamedView := { state.view with binders := newBinders }
  let isRegisteredExp ← replacementIsRealExpOf renamedView binderIndex replacement
  if (← get).messages.hasErrors then
    throwAbortCommand
  let positiveMatch? ← if isRegisteredExp then
      findPositiveConstraint state.view binderIndex
    else
      pure none
  let positiveIndex? := positiveMatch?.map (·.index)
  let normalizationUnfolds := match positiveMatch?.bind (·.unfold?) with
    | some name =>
        if state.normalizationUnfolds.contains name then
          state.normalizationUnfolds
        else
          state.normalizationUnfolds.push name
    | none => state.normalizationUnfolds

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
    let wasPresentedAsTrue ← constraintIsTypedTrue state.view index
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
        let source := state.source
        let sourceSimp ← liftMacroM `(
          Lean.Parser.Tactic.simpLemma| $source:term)
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
        let oldPattern ← liftMacroM <|
          mkProductPattern (state.view.binders.map fun binder => binder.name)
        let constraintBody ← liftMacroM <| mkConstraintConjunctionSyntax
          (state.view.constraints.toList.map fun constraint =>
            (⟨constraint.proposition⟩ : TSyntax `term))
        let canonicalFeasible ← liftMacroM `(
          fun ($oldPattern : $domainType) => $constraintBody)
        let feasibleIdent : TSyntax `ident := ⟨mkIdent `normalizedFeasible⟩
        let feasible : TSyntax `term := ⟨feasibleIdent.raw⟩
        let positiveEvidence ← liftMacroM <|
          mkConjunctionEvidence feasible positiveIndex state.view.constraints.size
        liftMacroM `(
          ({
            preimage := fun $pointIdent => $preimage
            rightInverse := fun $pointIdent => by
              have $feasibleIdent : ($canonicalFeasible) ($pointTerm).1 := by
                simpa only [$sourceSimp, PTran.Problem.pullback,
                  PTran.Problem.epigraph, PTran.Problem.hypograph,
                  Real.log_exp, Real.exp_pos, true_and, and_true,
                  and_assoc] using ($pointTerm).2
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
    normalizationUnfolds
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
  let newName ← inferNewBinder state.view oldName binderIndex replacement
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
    normalizationUnfolds := state.normalizationUnfolds
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

private def normalizationSimpLemmas (sourceTerm : TSyntax `term)
    (unfoldDeclarations : Array Name) :
    MacroM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let sourceLemma ← `(
    Lean.Parser.Tactic.simpLemma| $sourceTerm:term)
  let mut lemmas := #[sourceLemma]
  for declaration in unfoldDeclarations do
    lemmas := lemmas.push (← `(
      Lean.Parser.Tactic.simpLemma| $(mkIdent declaration):term))
  for declaration in #[``PTran.Problem.pullback, ``PTran.Problem.epigraph,
      ``PTran.Problem.hypograph, ``Real.log_exp, ``Real.exp_pos,
      ``true_and, ``and_true, ``and_assoc, ``eq_self, ``iff_self] do
    lemmas := lemmas.push (← `(
      Lean.Parser.Tactic.simpLemma| $(mkIdent declaration):term))
  pure lemmas

private def checkedPointwiseNormalization (sourceTerm : TSyntax `term)
    (semantic canonical : Expr) (unfoldDeclarations : Array Name) :
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
    normalizationSimpLemmas sourceTerm unfoldDeclarations
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

private def presentationDeltaBetween
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
        result.normalizationUnfolds
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
    normalizationUnfolds := surface.normalizationUnfolds
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
      normalizationSimpLemmas sourceTerm state.normalizationUnfolds
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
