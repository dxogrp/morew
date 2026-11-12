/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.State
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lean.Meta.Tactic.Simp.Main

/-! Stable syntax, canonical presentations, and normalization for steps and command emission. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

/-- Presentation rendering contexts. -/
inductive ViewMode where
  /-- Fully explicit, fixed-reference syntax. -/
  | exact
  /-- A compact display. -/
  | compact
  /-- A detailed display. -/
  | detailed

/-- Optional rendering functions for conic or NLP representations. -/
structure ViewHooks where
  /-- Select expression printers for the requested display format. -/
  options : ViewMode → Options → Options := fun _ => id
  /-- Expand a stored conic or NLP expression for display. -/
  prepareReadable : Expr → MetaM (Option Expr) := fun _ => pure none
  /-- Construct optional mathematical notation from the final typed constraints. -/
  mathematicalRows : Array Expr → (Expr → TermElabM Syntax) →
      TermElabM (Array (Option Morew.Syntax.PowerChainRow)) :=
    fun rows _ => pure (Array.replicate rows.size none)

private unsafe def mkViewAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute ViewHooks) :=
  KeyedDeclsAttribute.init {
    name := `morew_reformulation_view
    descr := "internal reformulation presentation provider"
    valueTypeName := ``ViewHooks
  } ref

@[implemented_by mkViewAttributeUnsafe]
private opaque mkViewAttribute (ref : Name) : IO (KeyedDeclsAttribute ViewHooks)

/-- Import-persistent internal presentation provider registry. -/
initialize viewAttribute : KeyedDeclsAttribute ViewHooks ← mkViewAttribute decl_name%

private def viewHooks : CoreM ViewHooks := do
  match viewAttribute.getValues (← getEnv) `presentation with
  | [] => pure {}
  | [hooks] => pure hooks
  | _ => throwError "multiple internal reformulation presentation providers registered"

-- Hide finite-index proofs only in compact output.
private def compactIndexProofsOption : Name :=
  `Morew.Elab.Reformulation.compactIndexProofs

-- Use coordinate notation only for display; syntax used to reconstruct expressions retains explicit fields.
private def coordinateNotationOption : Name :=
  `Morew.Elab.Reformulation.coordinateNotation

-- Mark bound proofs so their names can be omitted from compact output.
private def compactFiniteIndexProofs (expression : Expr) (replay : Bool) : MetaM Expr := do
  if replay || !(← getOptions).getBool compactIndexProofsOption then return expression
  -- Remove stored syntax annotations before locating finite-index constructors.
  let expression ← erasePatternRefAnnotations expression
  Meta.transform expression (post := fun value => do
    if value.isAppOfArity ``Fin.mk 3 then
      let args := value.getAppArgs
      return .done (mkAppN value.getAppFn #[args[0]!, args[1]!,
        mkAnnotation `Morew.Elab.Reformulation.compactFiniteIndexProof args[2]!])
    return .continue)

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

/-- Preserve readable spelling with fixed declaration identity and capture protection. -/
private def freezePresentationConstant (stx : Lean.Syntax) (name : Name) : Lean.Syntax :=
  match (mkCIdentFrom stx stx.getId).raw with
  | .ident info raw identifier _ => .ident info raw identifier [.decl name []]
  | _ => mkCIdentFrom stx name

private partial def freezePresentationReferences
    (infos : SubExpr.PosMap Elab.Info) (binders : Array (FVarId × Name))
    (sectionReferences : Std.HashMap FVarId Name)
    (parameterInstances : Std.HashMap FVarId Lean.Syntax)
    (stx : Lean.Syntax) : Lean.Syntax :=
  if let some id := annotatedFVarId? infos stx then
    match binders.find? fun entry => entry.1 == id with
    | some (_, name) => mkIdentFrom stx name
    | none => match sectionReferences.get? id with
      | some uid => mkCIdentFrom stx uid
      | none => (parameterInstances.get? id).getD stx
  else if let some name := annotatedConstName? infos stx then
    freezePresentationConstant stx name
  else
    stx.setArgs <| stx.getArgs.map fun child =>
      freezePresentationReferences infos binders sectionReferences parameterInstances child

/-- Use stable section-variable UIDs for transient semantic syntax. -/
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

private def stabilizeExpressionSyntax (expression : Expr) : TermElabM (TSyntax `term) := do
  let hooks ← viewHooks
  withOptions (fun options =>
      (hooks.options .exact options).set `pp.fullNames true |>.set `pp.privateNames true
        |>.set `pp.explicit true |>.set `pp.instances true
        |>.set `pp.proofs true |>.set `pp.tagAppFns true
        |>.set `pp.deepTerms true |>.set `pp.structureInstanceTypes true
        |>.set `pp.funBinderTypes true
        |>.set `pp.numericTypes true
        |>.set `pp.coercions false
        |>.set `pp.maxSteps (1000000 : Nat)
        |>.set `pp.fieldNotation false) do
    let (stable, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    pure ⟨freezeConstantReferences infos (← sectionReferenceNames) stable.raw⟩

/-- Delaborate an expression with explicit arguments and fixed constant references. -/
def exactExpressionSyntax (expression : Expr) : TermElabM (TSyntax `term) := do
  let hooks ← viewHooks
  withOptions (fun options => (hooks.options .exact options).set `pp.all true
      |>.set `pp.explicit true |>.set `pp.instances true
      |>.set `pp.proofs true |>.set `pp.deepTerms true
      |>.set `pp.structureInstances false |>.set `pp.beta true
      |>.set `pp.coercions false
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

/-- Readable binder types with fixed global references and persistent local names. -/
def presentationTypeSyntax (type : Expr) (replay : Bool := true)
    (parameterInstances : Std.HashMap FVarId Lean.Syntax := {}) : TermElabM Lean.Syntax := do
  let type ← compactFiniteIndexProofs type replay
  -- Retain explicit class projections in auxiliary types.
  withOptions (fun options =>
      let options := options.setBool `pp.tagAppFns true
      if replay then options.setBool `pp.proofs true |>.setBool `pp.instances true
        |>.setBool `pp.deepTerms true |>.setBool `pp.explicit true
        |>.setBool `pp.numericTypes true |>.setBool `pp.funBinderTypes true
        |>.setBool `pp.fieldNotation false
        |>.setBool `pp.coercions false
      else options) do
    let (stx, infos) ← PrettyPrinter.delabCore type {}
      PrettyPrinter.Delaborator.delab
    let sectionReferences ← if replay then sectionReferenceNames else pure {}
    pure <| freezePresentationReferences infos #[]
      sectionReferences parameterInstances stx.raw

/-- Stable syntax for the semantic decision and objective-value types. -/
structure ProblemTypeSyntax where
  /-- Stable semantic decision-domain type. -/
  domain : TSyntax `term
  /-- Stable semantic objective-value type. -/
  value : TSyntax `term

/-- Recover stable type syntax directly from an already checked problem. -/
def problemTypeSyntaxFromExpression (expression : Expr) :
    TermElabM ProblemTypeSyntax := do
  let type ← whnf (← inferType expression)
  unless type.getAppFn.isConstOf ``Morew.Problem &&
      type.getAppNumArgs == 2 do
    throwError "term does not have type `Morew.Problem _ _`"
  let domain := type.getAppArgs[0]!
  let value := type.getAppArgs[1]!
  pure {
    domain := ← exactExpressionSyntax domain
    value := ← exactExpressionSyntax value
  }

-- Preserve class operation heads and instances while simplifying operands and structure projections.
private def classOperationPrefix? (expression : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let .const name _ := expression.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  unless info.fromClass do return none
  let arguments := expression.getAppArgs
  let prefixSize := min arguments.size (info.numParams + 1)
  return some (mkAppN expression.getAppFn (arguments.extract 0 prefixSize),
    arguments.extract prefixSize arguments.size)

-- Reduce data lets explicitly and retain scoped proof lets.
private def presentationSimpMethods (preserveProofLets : Bool)
    (preserveOperations : Bool := true) : Simp.Methods :=
  let defaults := Simp.mkDefaultMethodsCore #[]
  { defaults with
    pre := fun expression => do
      if preserveOperations then
        if let some (function, arguments) ← classOperationPrefix? expression then
          -- Apply supplied rewrite lemmas while preserving the operation instance.
          match ← Simp.rewritePre (rflOnly := false) expression with
          | .visit result => return .visit result
          | .done result => return .done result
          | .continue _ => pure ()
          let result ← Simp.congrArgs { expr := function } arguments
          match ← Simp.rewritePost (rflOnly := false) result.expr with
          | .visit rewritten => return .visit (← result.mkEqTrans rewritten)
          | .done rewritten => return .done (← result.mkEqTrans rewritten)
          | .continue _ => return .done result
      if let .letE name type value body nondep := expression then
        unless preserveProofLets do return ← defaults.pre expression
        unless ← isProp type do
          return .visit { expr := body.instantiate1 value }
        -- Visit the body explicitly to retain proof scope and reduce following data lets.
        return ← withLetDecl name type value (nondep := nondep) fun binding => do
          let result ← Simp.simp (body.instantiate1 binding)
          let expr ← mkLetFVars #[binding] result.expr
            (usedLetOnly := false) (generalizeNondepLet := false)
          let proof? ← result.proof?.mapM fun proof =>
            mkLetFVars #[binding] proof
              (usedLetOnly := false) (generalizeNondepLet := false)
          return .done { result with expr, proof? }
      defaults.pre expression
    dpre := fun expression => do
      if preserveOperations then
        if let some (function, arguments) ← classOperationPrefix? expression then
          return .done (mkAppN function (← arguments.mapM Simp.dsimp))
      if let .letE name type value body nondep := expression then
        unless preserveProofLets do return ← defaults.dpre expression
        unless ← isProp type do
          return .visit (body.instantiate1 value)
        return ← withLetDecl name type value (nondep := nondep) fun binding => do
          let body ← Simp.dsimp (body.instantiate1 binding)
          return .done (← mkLetFVars #[binding] body
            (usedLetOnly := false) (generalizeNondepLet := false))
      defaults.dpre expression }

/-- Simplify an expression using only the supplied declarations and reductions.
Canonical predicates can retain scoped proof lets for later certification. -/
def simpOnly (expression : Expr) (lemmas : Array Name := #[])
    (unfold : Array Name := #[]) (preserveProofLets : Bool := false) : MetaM Expr := do
  let mut theorems : SimpTheorems := {}
  for declaration in lemmas do
    theorems ← theorems.addConst declaration
  for declaration in unfold do
    theorems ← theorems.addDeclToUnfold declaration
  let context ← Simp.mkContext
    (config := if preserveProofLets then { zeta := false, zetaUnused := false } else {})
    (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← Simp.main expression context
    (methods := presentationSimpMethods preserveProofLets)
  instantiateMVars result.expr

/-- Reduce generated structure while retaining evidence lets. Reduce operations only for
direct certification of a complete predicate. -/
def dsimpPreservingProofLets (expression : Expr)
    (preserveOperations : Bool := true) : MetaM Expr := do
  let context ← Simp.mkContext
    (config := { zeta := false, zetaUnused := false })
    (simpTheorems := #[{}]) (congrTheorems := ← getSimpCongrTheorems)
  let (expression, _) ← Simp.dsimpMain expression context
    (methods := presentationSimpMethods true preserveOperations)
  instantiateMVars expression

private partial def splitConstraintBody (body : Expr) (count : Nat) : MetaM (Array Expr) := do
  if let .letE name type value rest nondep := body.consumeMData then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let rows ← splitConstraintBody (rest.instantiate1 binding) count
      rows.mapM fun row => mkLetFVars #[binding] row
        (usedLetOnly := false) (generalizeNondepLet := false)
  match count with
  | 0 =>
      unless ← isDefEq body (mkConst ``True) do
        throwError "problem presentation metadata does not match the source feasibility predicate"
      pure #[]
  | 1 => pure #[body]
  | count + 2 =>
      let body ← withConfig (fun config => { config with zeta := false, zetaUnused := false }) <|
        whnf body
      if body.isLet then return ← splitConstraintBody body (count + 2)
      let arguments := body.getAppArgs
      unless body.getAppFn.isConstOf ``And && arguments.size == 2 do
        throwError "problem presentation metadata does not match the source constraint structure"
      let rest ← splitConstraintBody arguments[1]! (count + 1)
      pure <| #[arguments[0]!] ++ rest

private def sourceProblemParts (sourceName : Name) (source : Expr)
    (constraintCount : Nat) : MetaM
    (Expr × Expr × Array Expr) := do
  let sourceType ← whnf (← inferType source)
  unless sourceType.getAppFn.isConstOf ``Morew.Problem &&
      sourceType.getAppNumArgs == 2 do
    throwError "reformulation source does not have type `Morew.Problem _ _`"
  let domain := sourceType.getArg! 0
  let objective ← mkAppM ``Morew.Problem.objective #[source]
  let feasible ← mkAppM ``Morew.Problem.feasible #[source]
  let constraints ← withLocalDeclD `point domain fun point => do
    let body ← simpOnly (mkApp feasible point) (unfold := #[sourceName])
      (preserveProofLets := true)
    let bodies ← splitConstraintBody body constraintCount
    bodies.mapM fun body => mkLambdaFVars #[point] body
  pure (domain, objective, constraints)

/-- Replace the stored source problem at the start of the transformation sequence. -/
private partial def protectCheckpoint (expression checkpoint replacement : Expr) : MetaM Expr := do
  let expression := expression.consumeMData.headBeta
  if expression == checkpoint then return replacement
  if let .letE _ _ value body _ := expression then
    return ← protectCheckpoint (body.instantiate1 value) checkpoint replacement
  let arguments := expression.getAppArgs
  let isPullback := expression.isAppOfArity ``Morew.Problem.pullback 5
  let isBound := expression.isAppOfArity ``Morew.Problem.epigraph 4 ||
    expression.isAppOfArity ``Morew.Problem.hypograph 4
  unless isPullback || isBound do
    if ← isDefEq expression checkpoint then return replacement
    throwError "reformulation semantic problem does not extend its canonicalization checkpoint"
  let base ← protectCheckpoint arguments[3]! checkpoint replacement
  pure <| mkAppN expression.getAppFn (arguments.set! 3 base)

/-- Construct the canonical target while preserving the stored source constraints.
Use `sourceName` only to unfold the original problem container. -/
def canonicalTargetExpressionFromExpressions (sourceName : Name)
    (source semanticAnchor : Expr) (sourceView : Morew.Syntax.ProblemView)
    (removedCheckpointRows : Std.HashSet Nat) (semanticExpression : Expr)
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
      let protectedSource ← mkAppM ``Morew.Problem.mk
        #[protectedObjective, protectedFeasible]
      let protectedSemantic ← protectCheckpoint semanticExpression semanticAnchor protectedSource
      let transformed ← simpOnly protectedSemantic (unfold :=
        #[``Morew.Problem.pullback, ``Morew.Problem.epigraph,
          ``Morew.Problem.hypograph]) (preserveProofLets := true)

      -- Normalize protected objectives both as functions and at applications.
      let exactObjective ← simpOnly objective (unfold := #[sourceName])
        (preserveProofLets := true)
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
              (if simplifyExpLogTerms then #[``Real.log_exp, ``Real.exp_pos, ``sq_nonneg] else #[])
              (unfold := #[sourceName]) (preserveProofLets := true)
            let removedSourceConstraint := partIndex > 0 &&
              removedCheckpointRows.contains (partIndex - 1)
            if removedSourceConstraint then
              -- Replace removed rows by `True` using the step's normalization evidence.
              pure (.done (mkConst ``True))
            else
              let placeholder ← mkFreshExprMVar (some (← inferType exact))
                (kind := .syntheticOpaque)
              modify fun assignments =>
                assignments.push (placeholder.mvarId!, exact)
              pure (.done placeholder))
      let (transformedProtected, assignments) ← protectAction.run #[]
      let normalized ← simpOnly transformedProtected
        #[``true_and, ``and_true, ``and_assoc] (preserveProofLets := true)
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

/-- Elaborate a source and transformation sequence, then normalize their checked
expressions while preserving the stored source constraints and their order. -/
def canonicalTargetExpression (sourceName : Name)
    (sourceTerm semanticAnchorTerm : TSyntax `term) (sourceView : Morew.Syntax.ProblemView)
    (removedCheckpointRows : Std.HashSet Nat) (semantic : TSyntax `term)
    (simplifyExpLogTerms : Bool) : TermElabM Expr := do
  let source ← elabTerm sourceTerm none
  synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let semanticAnchor ← elabTerm semanticAnchorTerm none
  synthesizeSyntheticMVarsNoPostponing
  let semanticAnchor ← instantiateMVars semanticAnchor
  let semanticExpression ← elabTerm semantic none
  synthesizeSyntheticMVarsNoPostponing
  let semanticExpression ← instantiateMVars semanticExpression
  canonicalTargetExpressionFromExpressions sourceName source semanticAnchor sourceView
    removedCheckpointRows semanticExpression simplifyExpLogTerms

private partial def splitProductDomain (domain : Expr) : Nat → MetaM (Array Expr)
  | 0 => throwError "a problem presentation requires at least one optimization variable"
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
    throwError "a problem presentation requires at least one optimization variable"

/-- Internal rendering flag for stored presentations. -/
def presentationNotationOption : Name := `Morew.Elab.Reformulation.presentationNotation

-- Print operations explicitly when notation would choose different instances.
/-- Check whether ordinary notation would recover the stored operation instance. -/
def presentationInstanceResynthesizes (stored : Expr) : MetaM Bool :=
  withoutModifyingState do
    match ← trySynthInstance (← inferType stored) with
    | .some inferred => isDefEq stored inferred
    | _ => pure false

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.WithLp.ofLp]
private def delabLpCoordinate : Delab := do
  let options ← getOptions
  unless options.getBool coordinateNotationOption && !options.getBool `pp.explicit do failure
  withOverApp 4 do
    let expression ← getExpr
    guard <| expression.isAppOfArity ``WithLp.ofLp 4
    let args := expression.getAppArgs
    let domain ← inferType args[2]!
    let functionType := Lean.mkLambda `_ .default domain args[1]!
    let projection := mkAppN expression.getAppFn (args.extract 0 2)
    let canonical ← mkAppOptM ``CoeFun.mk
      #[some domain, some functionType, some projection]
    guard (← presentationInstanceResynthesizes canonical)
    let value ← withNaryArg 2 delab
    let index ← withNaryArg 3 delab
    `($value $index)

private def presentationSingletonMembership {Y : Type} (value zero : Y) : Prop :=
  value ∈ ({zero} : Set Y)

-- Annotate singleton sets with their `Set` type so stored syntax can be elaborated unambiguously.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Membership.mem]
private def delabZeroSetMembership : Delab := do
  unless (← getOptions).getBool presentationNotationOption &&
      !(← getOptions).getBool `pp.explicit do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``Membership.mem 5
  let args := expression.getAppArgs
  guard <| (← whnfUntil args[1]! ``Set).isSome
  let target ← whnf args[0]!
  unless target.isConstOf ``Real do
    let .forallE _ index range _ := target | failure
    let range ← whnf range
    guard <| !range.hasLooseBVars && range.isConstOf ``Real &&
      (← whnf index).isAppOfArity ``Fin 1
  let singleton := args[3]!.consumeMData
  guard <| singleton.isAppOfArity ``Singleton.singleton 4
  let singletonArgs := singleton.getAppArgs
  let zero := singletonArgs[3]!.consumeMData
  guard <| zero.isAppOfArity ``Zero.zero 2 ||
    (zero.isAppOfArity ``OfNat.ofNat 3 &&
      (zero.getAppArgs[1]! == mkRawNatLit 0 || zero.getAppArgs[1]! == mkNatLit 0))
  let template ← mkAppM ``presentationSingletonMembership #[args[4]!, zero]
  let some template ← unfoldDefinition? template | failure
  let canonical := template.getAppArgs
  guard (← isDefEq args[2]! canonical[2]!)
  guard (← isDefEq singletonArgs[2]! canonical[3]!.getAppArgs[2]!)
  let zeroInstance := zero.getAppArgs[if zero.isAppOfArity ``Zero.zero 2 then 1 else 2]!
  unless (← presentationInstanceResynthesizes args[2]!) &&
      (← presentationInstanceResynthesizes singletonArgs[2]!) &&
      (← presentationInstanceResynthesizes zeroInstance) do
    return ← withOptions (fun options => options.setBool `pp.explicit true
      |>.setBool `pp.instances true) delabApp
  let value ← withNaryArg 4 delab
  let set ← withNaryArg 3 delab
  let type ← withNaryArg 1 delab
  `($value ∈ ($set : $type))

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
private def delabStoredInstance (arity instanceIndex : Nat) : Delab := do
  unless (← getOptions).getBool presentationNotationOption &&
      !(← getOptions).getBool `pp.explicit do failure
  withOverApp arity do
    let stored := (← getExpr).getAppArgs[instanceIndex]!
    if ← presentationInstanceResynthesizes stored then failure
    withOptions (fun options => options.setBool `pp.explicit true
      |>.setBool `pp.instances true) delabApp

open Lean.PrettyPrinter.Delaborator in
@[delab app.HSub.hSub]
private def delabStoredSubtraction : Delab := delabStoredInstance 6 3

open Lean.PrettyPrinter.Delaborator in
@[delab app.Neg.neg]
private def delabStoredNegation : Delab := delabStoredInstance 3 1

open Lean.PrettyPrinter.Delaborator in
@[delab app.Zero.zero]
private def delabStoredZero : Delab := delabStoredInstance 2 1

open Lean.PrettyPrinter.Delaborator in
@[delab app.OfNat.ofNat]
private def delabStoredNumeral : Delab := delabStoredInstance 3 2

open Lean.PrettyPrinter.Delaborator in
@[delab app.Membership.mem]
private def delabStoredMembership : Delab := delabStoredInstance 5 2

open Lean.PrettyPrinter.Delaborator in
@[delab app.Singleton.singleton]
private def delabStoredSingleton : Delab := delabStoredInstance 4 2

/-- Render with fixed global references and supplied binding names. -/
def delabPresentationTerm (expression : Expr)
    (binders : Array (FVarId × Name)) (replay : Bool := true)
    (parameterInstances : Std.HashMap FVarId Lean.Syntax := {}) : TermElabM Lean.Syntax := do
  let hooks ← viewHooks
  -- Omit unused analytic proof bindings only from display syntax.
  let expression ← if replay then pure expression else
    Meta.transform expression (pre := fun expression => do
      if let some prepared ← hooks.prepareReadable expression then
        return .visit prepared
      if let .letE _ type value body _ := expression then
        if !body.hasLooseBVar 0 && (← isProp type) then
          return .visit (body.instantiate1 value)
      return .continue)
  let expression ← compactFiniteIndexProofs expression replay
  -- Reserve visible model names before naming inner binders.
  withLCtx' (binders.foldl (fun context (id, name) =>
      context.setUserName id name.eraseMacroScopes) (← getLCtx)) do
  -- Retain explicit constant references and implicit arguments, including class projections.
  withOptions (fun options =>
      let options := options.setBool presentationNotationOption true |>.setBool `pp.tagAppFns true
        |>.setBool `pp.coercions.types true |>.setBool `pp.beta false
      if replay then options.setBool `pp.proofs true |>.setBool `pp.instances true
        |>.setBool `pp.deepTerms true |>.setBool `pp.explicit true
        |>.setBool `pp.funBinderTypes true |>.setBool `pp.numericTypes true
        |>.setBool `pp.structureInstanceTypes true |>.setBool `pp.fieldNotation false
        -- Omitting a field equal to its default can erase direct occurrences.
        |>.setBool `pp.structureInstances.defaults true
        -- Cast notation would infer coercions again when the stored syntax is elaborated.
        |>.setBool `pp.coercions false
      else options) do
    let (stx, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    let sectionReferences ← if replay then sectionReferenceNames else pure {}
    pure <| freezePresentationReferences infos binders
      sectionReferences parameterInstances stx.raw

/-- Elaborate sequential model definitions as let-bound locals under decision binders. -/
def withViewDefinitions (view : Morew.Syntax.ProblemView)
    (action : Array Expr → TermElabM α) : TermElabM α := do
  let rec /-- Elaborate each definition in the scope of its predecessors. -/
      visit (remaining : List Morew.Syntax.DefinitionView) (bindings : Array Expr) := do
    match remaining with
    | [] => action bindings
    | definition :: remaining =>
        let type? ← (definition.typeSyntax?.or definition.inferredTypeSyntax?).mapM elabType
        let value ← match type? with
          | some type => elabTermEnsuringType definition.value type
          | none => elabTerm definition.value none
        synthesizeSyntheticMVarsNoPostponing
        let value ← instantiateMVars value
        if value.hasMVar then
          throwErrorAt definition.value "model-local definition contains unresolved metavariables"
        let type ← instantiateMVars (← inferType value)
        withLetDecl definition.name type value fun binding =>
          visit remaining (bindings.push binding)
  visit view.definitions.toList #[]

/-- Elaborate under temporary aliases for displayed bindings, then restore binding identities.
Retain global references captured by macros. -/
partial def elabPresentationTerm (term : TSyntax `term) (bindings : Array Expr)
    (expectedType? : Option Expr := none) : TermElabM Expr := do
  let names ← bindings.mapM fun binding => do
    return ((← binding.fvarId!.getDecl).userName, binding)
  let rec /-- Collect the scoped aliases needed by the term's local references. -/
      collect (stx : Syntax) (aliases : NameMap Expr) : NameMap Expr := Id.run do
    let mut aliases := aliases
    if let .ident _ _ name resolved := stx then
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
  let rec /-- Elaborate under temporary aliases and restore the original bindings. -/
      elaborate (remaining : List (Name × Expr)) (aliases values : Array Expr) :
      TermElabM Expr := do
    match remaining with
    | [] =>
        let expression ← elabTerm term expectedType?
        synthesizeSyntheticMVarsNoPostponing
        return (← instantiateMVars expression).replaceFVars aliases values
    | (name, value) :: remaining =>
        withLetDecl name (← inferType value) value fun temporary =>
          elaborate remaining (aliases.push temporary) (values.push value)
  elaborate (collect term.raw {}).toList #[] #[]

/-- Recognize projections of the synthetic decision point only. -/
private partial def decisionProjection? (point : Expr) (count : Nat)
    (expression : Expr) : Option (Nat × Nat) := do
  let expression := expression.consumeMData
  if expression == point then return (0, count)
  let (index, argument) ← match expression with
    | .proj ``Prod index argument => some (index, argument)
    | _ =>
        if expression.isAppOfArity ``Prod.fst 3 then
          some (0, expression.getArg! 2)
        else if expression.isAppOfArity ``Prod.snd 3 then
          some (1, expression.getArg! 2)
        else none
  let (start, size) ← decisionProjection? point count argument
  guard (size > 1)
  match index with
  | 0 => some (start, size - 1)
  | 1 => some (start + size - 1, 1)
  | _ => none

/-- Open the outer decision lambda and tuple pattern while preserving user-body occurrences. -/
private def openPresentationBody (function domain : Expr) (binders : Array Expr) :
    MetaM Expr := do
  let .lam _ _ body _ := (← whnf function).consumeMData
    | throwError "problem presentation field is not a decision function"
  withLocalDeclD `presentationPoint domain fun point => do
    let mut body := body.instantiate1 point
    if binders.size > 1 then
      if let some matcher ← matchMatcherApp? body.consumeMData then
        if matcher.discrs == #[point] && matcher.alts.size == 1 &&
            matcher.remaining.isEmpty && matcher.altNumParams[0]! == binders.size then
          let mut alternative := matcher.alts[0]!
          for binder in binders do
            let .lam _ _ rest _ := alternative.consumeMData
              | throwError "problem presentation has an invalid decision tuple pattern"
            alternative := rest.instantiate1 binder
          body := alternative
    Meta.transform body (pre := fun expression => do
      -- Recover function-valued decision projections before visiting their application arguments.
      let (projection, arguments) :=
        if (expression.isAppOf ``Prod.fst || expression.isAppOf ``Prod.snd) &&
            expression.getAppNumArgs > 3 then
          let arguments := expression.getAppArgs
          (mkAppN expression.getAppFn (arguments.extract 0 3), arguments.extract 3 arguments.size)
        else (expression, #[])
      if let some (start, size) := decisionProjection? point binders.size projection then
        let replacement ← packPoint (binders.extract start (start + size))
        if arguments.isEmpty then return .done replacement
        return .continue (some (mkAppN replacement arguments))
      return .continue)

/-- Read paired definition sequences with shared opaque locals, preserving distinct binding identities. -/
private def withModelDefinitionBodies {α : Type} (template : Morew.Syntax.ProblemView)
    (objective feasible : Expr) (names : Array (FVarId × Name))
    (replay : Bool) (parameterInstances : Std.HashMap FVarId Lean.Syntax)
    (action : Array Morew.Syntax.DefinitionView → Expr → Expr →
      Array (FVarId × Name) → TermElabM α) :
    TermElabM α := do
  let rec visit (remaining : List Morew.Syntax.DefinitionView)
      (definitions : Array Morew.Syntax.DefinitionView)
      (objective feasible : Expr) (names : Array (FVarId × Name)) :
      TermElabM α := do
    let definition :: remaining := remaining
      | return ← action definitions objective feasible names
    let .letE _ type value body _ := objective.consumeMData
      | throwError "problem presentation lost model-local definition `{definition.name.eraseMacroScopes}`"
    let .letE _ feasibleType feasibleValue feasibleBody _ := feasible.consumeMData
      | throwError "problem feasibility presentation lost its model-local definition spine"
    unless (← isDefEq type feasibleType) && (← isDefEq value feasibleValue) do
      throwError "problem objective and feasibility disagree on a model-local definition"
    let definition := { definition with
      value := ← delabPresentationTerm value names replay parameterInstances
      typeSyntax? := ← definition.typeSyntax?.mapM fun _ =>
        delabPresentationTerm type names replay parameterInstances
      inferredTypeSyntax? := some (← delabPresentationTerm type names replay parameterInstances) }
    withLocalDeclD definition.name type fun binding =>
      visit remaining (definitions.push definition)
        (body.instantiate1 binding) (feasibleBody.instantiate1 binding)
        (names.push (binding.fvarId!, definition.name))
  visit template.definitions.toList #[] objective feasible names

-- Inspect typed constraints in their context; store syntax with fixed references.
private def problemViewWithRowsFromExpression {α : Type} [Inhabited α]
    (inspectRows : Array Expr → Array (FVarId × Name) → TermElabM α) (target : Expr)
    (template : Morew.Syntax.ProblemView) (instantiateBinderTypes : Bool := false)
    (recoverDefinitions : Bool := true) (forRegistration : Bool := false)
    (parameterInstances : Std.HashMap FVarId Lean.Syntax := {}) :
    TermElabM (Morew.Syntax.ProblemView × α) := do
  let targetType ← whnf (← inferType target)
  unless targetType.getAppFn.isConstOf ``Morew.Problem &&
      targetType.getAppNumArgs == 2 do
    throwError "reformulation target does not have type `Morew.Problem _ _`"
  -- Reduce the source container to `Problem.mk` while preserving field bodies and bindings.
  let target ← if recoverDefinitions then
      withTransparency .all <| whnf target
    else pure target
  let domain := targetType.getArg! 0
  let binderTypes ← splitProductDomain domain template.binders.size
  let compactTypes := forRegistration && (← getOptions).getBool compactIndexProofsOption
  let displayedBinders ← template.binders.mapIdxM fun index binder => do
    -- Retain named types; inspect finite-index constructors to identify proofs omitted from compact output.
    let binderType ← if compactTypes then erasePatternRefAnnotations binderTypes[index]!
      else pure binderTypes[index]!
    let hasFiniteConstructor := (binderType.find?
      (·.isAppOfArity ``Fin.mk 3)).isSome
    if instantiateBinderTypes || (compactTypes && hasFiniteConstructor) then
      pure { binder with
        typeSyntax := ← presentationTypeSyntax binderType
          (!forRegistration) parameterInstances }
    else
      pure binder
  let binderDeclarations := binderTypes.mapIdx fun index type =>
    (template.binders[index]!.name, type)
  withLocalDeclsDND binderDeclarations fun binders => do
    let point ← packPoint binders
    let objective ← mkAppM ``Morew.Problem.objective #[target]
    let feasible ← mkAppM ``Morew.Problem.feasible #[target]
    let binderNames := binders.mapIdx fun index binder =>
      (binder.fvarId!, template.binders[index]!.name)
    let render definitions objectiveBody feasibleBody binderNames := do
      -- Use definitional reduction to preserve sum-index names.
      let objectiveBody ← if recoverDefinitions then pure objectiveBody else
        dsimpPreservingProofLets objectiveBody
      let feasibleBody ← if recoverDefinitions then pure feasibleBody else
        dsimpPreservingProofLets feasibleBody
      let constraints ← splitConstraintBody feasibleBody template.constraints.size
      let objectiveSyntax ← delabPresentationTerm objectiveBody binderNames
        (!forRegistration) parameterInstances
      let constraintSyntax ← constraints.mapM fun proposition =>
        delabPresentationTerm proposition binderNames (!forRegistration) parameterInstances
      let view := {
        template with
        binders := displayedBinders
        definitions
        objective := objectiveSyntax
        constraints := template.constraints.mapIdx fun index constraint =>
          { constraint with proposition := constraintSyntax[index]! }
      }
      return (view, ← inspectRows constraints binderNames)
    if recoverDefinitions then
      let objectiveBody ← openPresentationBody objective domain binders
      let feasibleBody ← openPresentationBody feasible domain binders
      withModelDefinitionBodies template objectiveBody feasibleBody
        binderNames (!forRegistration) parameterInstances render
    else
      render template.definitions (mkApp objective point) (mkApp feasible point) binderNames

/-- Recover printable bodies with ordered names. Instantiate applied-source binder types;
retain existing bare-name source spelling. -/
def problemViewFromExpression (target : Expr)
    (template : Morew.Syntax.ProblemView) (instantiateBinderTypes : Bool := false)
    (recoverDefinitions : Bool := true) (forRegistration : Bool := false)
    (parameterInstances : Std.HashMap FVarId Lean.Syntax := {}) :
    TermElabM Morew.Syntax.ProblemView := do
  return (← problemViewWithRowsFromExpression (fun _ _ => pure ()) target template
    instantiateBinderTypes recoverDefinitions forRegistration parameterInstances).1

/-- Recover a typed presentation from a checked problem expression. -/
def typedPresentationFromExpression (target : Expr)
    (template : Morew.Syntax.ProblemView) :
    TermElabM Morew.Elab.Reformulation.PresentationState := do
  let targetType ← whnf (← inferType target)
  unless targetType.getAppFn.isConstOf ``Morew.Problem &&
      targetType.getAppNumArgs == 2 do
    throwError "reformulation presentation target is not a `Morew.Problem`"
  let domain := targetType.getAppArgs[0]!
  let value := targetType.getAppArgs[1]!
  let binderTypes ← splitProductDomain domain template.binders.size
  let objective ← mkAppM ``Morew.Problem.objective #[target]
  let feasible ← mkAppM ``Morew.Problem.feasible #[target]
  let constraintPredicates ← withLocalDeclD `point domain fun point => do
    let feasibleBody ← simpOnly (mkApp feasible point) (preserveProofLets := true)
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

/-- Register syntax for reconstruction and display from the same generated
declaration and ordered parameters. -/
def refreshProblemView (targetName : Name)
    (template : Morew.Syntax.ProblemView) (instantiateBinderTypes : Bool := false) :
    CommandElabM Unit := do
  let hooks ← liftCoreM viewHooks
  let (refreshed, displayed, printed) ← runTermElabM fun _ => do
    -- Render using the declaration's own parameters for persistent metadata.
    let info ← getConstInfo targetName
    let target := Lean.mkConst targetName (info.levelParams.map Level.param)
    withLCtx {} {} do
      forallTelescopeReducing info.type (fun parameters _ => do
        -- Record instance identities before choosing printable parameter names.
        let anonymousInstances ← parameters.filterM fun parameter => do
          let declaration ← parameter.fvarId!.getDecl
          pure <| declaration.binderInfo == .instImplicit &&
            declaration.userName.hasMacroScopes &&
            declaration.userName.eraseMacroScopes == `inst
        let mut synthesizedInstanceIds : Std.HashSet FVarId := {}
        for parameter in anonymousInstances do
          synthesizedInstanceIds := synthesizedInstanceIds.insert parameter.fvarId!
        -- Choose consistent distinct parameter names, reserving model and parameter names before freshening.
        let parameterNames ← parameters.mapM fun parameter =>
          return (← parameter.fvarId!.getDecl).userName.eraseMacroScopes
        let decisionNames := template.binders.foldl
          (fun names binder => names.insert binder.name.eraseMacroScopes) ({} : NameSet)
        let decisionNames := template.definitions.foldl
          (fun names definition => names.insert definition.name.eraseMacroScopes) decisionNames
        -- Use hygiene to separate colliding model bindings and parameters in exact syntax.
        let mut namedInstanceReferences : Std.HashMap FVarId Lean.Syntax := {}
        let mut replayScopedNames : NameSet := {}
        for parameter in parameters, name in parameterNames do
          let declaration ← parameter.fvarId!.getDecl
          if declaration.binderInfo == .instImplicit &&
              !synthesizedInstanceIds.contains parameter.fvarId! &&
              decisionNames.contains name then
            namedInstanceReferences := namedInstanceReferences.insert parameter.fvarId!
              (mkIdent name)
            replayScopedNames := replayScopedNames.insert name
        let replayBinders ← template.binders.mapM fun binder => do
          unless replayScopedNames.contains binder.name.eraseMacroScopes do return binder
          let name ← withFreshMacroScope do MonadQuotation.addMacroScope binder.name
          return { binder with name }
        let replayDefinitions ← template.definitions.mapM fun definition => do
          unless replayScopedNames.contains definition.name.eraseMacroScopes do return definition
          let name ← withFreshMacroScope do MonadQuotation.addMacroScope definition.name
          return { definition with name }
        let replayTemplate := { template with
          binders := replayBinders, definitions := replayDefinitions }
        let reserved := parameterNames.foldl (fun names name => names.insert name) decisionNames
        let mut occupied := decisionNames
        let mut lctx ← getLCtx
        for parameter in parameters, name in parameterNames do
          let mut displayName := name
          if occupied.contains displayName then
            let mut index := 1
            displayName := name.appendIndexAfter index
            while reserved.contains displayName || occupied.contains displayName do
              index := index + 1
              displayName := name.appendIndexAfter index
            if (← parameter.fvarId!.getDecl).binderInfo == .instImplicit &&
                !namedInstanceReferences.contains parameter.fvarId! then
              synthesizedInstanceIds := synthesizedInstanceIds.insert parameter.fvarId!
          occupied := occupied.insert displayName
          lctx := lctx.setUserName parameter.fvarId! displayName
        let target := mkAppN target parameters
        let some target ← unfoldDefinition? target
          | throwError "cannot inspect reformulation target `{targetName}`"
        withLCtx' lctx do
          -- Reconstruct instance parameters by local identity or imported class type in parameter order.
          -- Keep the selected operation instances explicit.
          let mut parameterInstances : Std.HashMap FVarId Lean.Syntax := {}
          for parameter in parameters, name in parameterNames do
            unless (← parameter.fvarId!.getDecl).binderInfo == .instImplicit do continue
            let type : TSyntax `term := ⟨← presentationTypeSyntax (← inferType parameter)
              (parameterInstances := parameterInstances)⟩
            let reference ← if synthesizedInstanceIds.contains parameter.fvarId! then
                `((inferInstance : $type))
              else
                `(morew_replay_instance% $(mkIdent name) : $type)
            parameterInstances := parameterInstances.insert parameter.fvarId! reference.raw
          let replay ← problemViewFromExpression target replayTemplate (instantiateBinderTypes := true)
            (parameterInstances := parameterInstances)
          let display ← problemViewFromExpression target template instantiateBinderTypes
            (forRegistration := true)
          let (compact, mathematicalRows) ← withOptions (fun options =>
              (hooks.options .compact options).setBool `pp.proofs false
                |>.set `pp.proofs.threshold (0 : Nat) |>.setBool compactIndexProofsOption true
                |>.setBool coordinateNotationOption true) do
            problemViewWithRowsFromExpression (fun rows names =>
              hooks.mathematicalRows rows (fun expression =>
                delabPresentationTerm expression names false)) target template instantiateBinderTypes
              (forRegistration := true)
          let detailed ← withOptions (fun options =>
              (hooks.options .detailed options).setBool `pp.proofs true
                |>.setBool coordinateNotationOption true) do
              problemViewFromExpression target template instantiateBinderTypes
                (forRegistration := true)
          pure (replay, display,
            { compact, detailed, mathematicalRows : Morew.Syntax.ProblemPrintPresentation }))
  Morew.Syntax.registerProblemView targetName refreshed (some displayed) (some printed)

/-- Replace section variables in the stored problem description with those from the current context. -/
def withTypedPresentation (state : ReformState)
    (action : Morew.Elab.Reformulation.PresentationState → TermElabM α) :
    CommandElabM α :=
  runTermElabM fun sectionFVars =>
    action <| state.typed.presentation.replaceFVars state.sectionFVars sectionFVars

/-- Run an elaboration action under the presentation's typed decision binders. -/
def withPresentationBinders [Inhabited α]
    (presentation : Morew.Elab.Reformulation.PresentationState)
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
  for declaration in #[``Morew.Problem.pullback, ``Morew.Problem.epigraph,
      ``Morew.Problem.hypograph, ``Real.log_exp, ``Real.exp_pos, ``sq_nonneg,
      ``true_and, ``and_true, ``and_assoc, ``eq_self, ``iff_self] do
    lemmas := lemmas.push (← `(
      Lean.Parser.Tactic.simpLemma| $(mkIdent declaration):term))
  pure lemmas

/-- Construct and check normalization from semantic to canonical problems. -/
def checkedPointwiseNormalization (sourceName : Name)
    (semantic canonical : Expr) (predicateLemmas : Array (TSyntax `term)) :
    TermElabM Morew.Elab.Reformulation.PointwiseNormalization := do
  let semanticType ← whnf (← inferType semantic)
  let canonicalType ← whnf (← inferType canonical)
  unless semanticType.getAppFn.isConstOf ``Morew.Problem &&
      semanticType.getAppNumArgs == 2 &&
      canonicalType.getAppFn.isConstOf ``Morew.Problem &&
      canonicalType.getAppNumArgs == 2 do
    throwError "pointwise normalization requires two optimization problems"
  let domain := semanticType.getAppArgs[0]!
  unless ← isDefEq domain canonicalType.getAppArgs[0]! do
    throwError "pointwise normalization changed the decision domain"
  unless ← isDefEq semanticType.getAppArgs[1]! canonicalType.getAppArgs[1]! do
    throwError "pointwise normalization changed the objective value type"
  let semanticObjective ← mkAppM ``Morew.Problem.objective #[semantic]
  let canonicalObjective ← mkAppM ``Morew.Problem.objective #[canonical]
  let semanticFeasible ← mkAppM ``Morew.Problem.feasible #[semantic]
  let canonicalFeasible ← mkAppM ``Morew.Problem.feasible #[canonical]
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
  let equiv ← mkAppM ``Morew.pointwiseEquiv
    #[semantic, canonical, objectiveEquality, feasibleIff]
  let normalization : Morew.Elab.Reformulation.PointwiseNormalization := {
    semantic
    canonical
    objectiveEquality
    feasibleIff
    equiv
  }
  normalization.check
  pure normalization

/-- Describe the checked binder, objective, and constraint presentation changes. -/
def presentationDeltaBetween
    (current next : Morew.Elab.Reformulation.PresentationState)
    (objectiveEquality feasibleIff : Expr)
    (constraintSplices : Array ConstraintSplice := #[]) :
    MetaM Morew.Elab.Reformulation.PresentationDelta := do
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
        unless sameVisibleName current.constraints[index]!.name next.constraints[offset]!.name do
          throwError "constraint splice changed the order of an unselected constraint"
      ranges := ranges.push (offset, count)
      offset := offset + count
    unless offset == next.constraints.size do
      throwError "constraint splice does not match the next presentation shape"
  if next.binders.size < current.binders.size then
    throwError "reformulation steps cannot remove optimization-variable binders"
  let mut binderReplacements := #[]
  for index in [:current.binders.size] do
    let oldBinder := current.binders[index]!
    let newBinder := next.binders[index]!
    unless ← isDefEq oldBinder.type newBinder.type do
      throwError "reformulation changed the type of optimization variable `{oldBinder.name}`"
    unless sameVisibleName oldBinder.name newBinder.name do
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
      sameVisibleName candidate.name currentConstraint.name
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
        sameVisibleName candidate.name constraint.name do
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

end Morew.Elab.Reformulation
