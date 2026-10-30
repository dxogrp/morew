/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax.Presentation

/-!
# Problem term elaboration

Elaborate minimization and maximization terms into semantic problems and
register their source presentations. Public elaborator names remain in `Morew`.
-/

namespace Morew

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Parser

private def decodeBinder (stx : Lean.Syntax) : MacroM (Array Morew.Syntax.BinderView) := do
  match stx with
  | `(problemBinder| ($names:ident* : $typeSyntax:term)) =>
      pure <| names.map fun name => { name := name.getId, typeSyntax := typeSyntax }
  | _ => Macro.throwErrorAt stx "invalid problem binder"

private def decodeConstraint (stx : Lean.Syntax) : MacroM Morew.Syntax.ConstraintView := do
  match stx with
  | `(problemConstraint| $name:ident : $proposition:term) =>
      pure { name := name.getId, proposition := proposition }
  | _ => Macro.throwErrorAt stx "invalid named constraint"

private def decodeDefinition (stx : Lean.Syntax) : MacroM Morew.Syntax.DefinitionView := do
  match stx with
  | `(problemDefinition| let $name:ident $[: $type:term]? := $value:term) =>
      pure { name := name.getId, typeSyntax? := type.map (·.raw), value }
  | _ => Macro.throwErrorAt stx "invalid model-local definition"

private def mkProductType : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => Macro.throwError "a problem requires at least one decision variable"
  | first :: rest => rest.foldlM (fun accumulated typeSyntax => do
      `($accumulated × $typeSyntax)) first

private def mkProductPattern : List (TSyntax `ident) → MacroM (TSyntax `term)
  | [] => Macro.throwError "a problem requires at least one decision variable"
  | first :: rest =>
      let restTerms : List (TSyntax `term) := rest.map fun name => ⟨name.raw⟩
      restTerms.foldlM (fun accumulated name => do
        `(⟨$accumulated, $name⟩)) ⟨first.raw⟩

private partial def mkConstraintConjunction : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `(True)
  | [proposition] => pure proposition
  | proposition :: rest => do
      let tail ← mkConstraintConjunction rest
      `($proposition ∧ $tail)

private def ensureDistinct (what : String) (names : Array Name) (refs : Array Lean.Syntax) :
    MacroM Unit := do
  for i in [:names.size] do
    for j in [0:i] do
      if names[i]!.eraseMacroScopes == names[j]!.eraseMacroScopes then
        Macro.throwErrorAt refs[i]!
          s!"duplicate {what} name `{names[i]!.eraseMacroScopes}`"

private def decisionProjections (point : Expr) : Nat → MetaM (Array Expr)
  | 0 => throwError "a problem requires at least one decision variable"
  | 1 => pure #[point]
  | count + 2 => do
      let first ← mkAppM ``Prod.fst #[point]
      let previous ← decisionProjections first (count + 1)
      return previous.push (← mkAppM ``Prod.snd #[point])

private def decisionTypes (domain : Expr) : Nat → MetaM (Array Expr)
  | 0 => throwError "a problem requires at least one decision variable"
  | 1 => pure #[domain]
  | count + 2 => do
      let domain ← whnf domain
      unless domain.isAppOfArity ``Prod 2 do
        throwError "internal error: model decision domain is not a product"
      let previous ← decisionTypes (domain.getArg! 0) (count + 1)
      return previous.push (domain.getArg! 1)

private partial def splitModelPair (expression : Expr) : TermElabM (Expr × Expr) := do
  match expression with
  | .letE name type value body nondep =>
      let (objective, feasible) ← splitModelPair body
      pure (.letE name type value objective nondep, .letE name type value feasible nondep)
  | .mdata data body =>
      let (objective, feasible) ← splitModelPair body
      pure (.mdata data objective, .mdata data feasible)
  | _ =>
      unless expression.isAppOfArity ``Prod.mk 4 do
        throwError "internal error: model-local body is not an objective/feasibility pair"
      pure (expression.getArg! 2, expression.getArg! 3)

-- Original source views normally retain their spelling. Norm notation is
-- instance-sensitive, so its replay copy must retain the instance selected by
-- the source elaboration. The readable view continues to use the original term.
private partial def freezeNormReplayReferences (infos : SubExpr.PosMap Elab.Info)
    (explicitUniverses : Array (Expr × Lean.Syntax))
    (stx : Lean.Syntax) : TermElabM Lean.Syntax := do
  if let .ident (.synthetic start _ _) _ _ _ := stx then
    let termInfo? := match infos.get? start.byteIdx with
      | some (.ofTermInfo info) => some info
      | some (.ofDelabTermInfo info) => some info.toTermInfo
      | _ => none
    if let some info := termInfo? then
      match info.expr with
      | .const name _ =>
          if let some (_, source) := explicitUniverses.find? (·.1 == info.expr) then
            return source
          return mkCIdentFrom stx name
      | .fvar id =>
          -- Delaboration introduces fresh locals beneath lambda operands. Their
          -- printed names already respect shadowing and belong to that syntax,
          -- not to the original source local context.
          let some declaration := (← getLCtx).find? id | return stx
          if let some value := declaration.value? (allowNondep := true) then
            if (← isClass? declaration.type).isSome then
              -- Anonymous `letI` names are recreated at replay. Preserve the
              -- selected instance's value rather than a transient binder name.
              let (value, valueInfos) ← PrettyPrinter.delabCore value {}
                PrettyPrinter.Delaborator.delab
              return ← freezeNormReplayReferences valueInfos explicitUniverses value.raw
          -- Replay retains the source binder's macro scopes. References must
          -- keep the same identity, including in whole-problem macros.
          let name := mkIdentFrom stx declaration.userName
          if declaration.binderInfo.isInstImplicit then
            let (type, typeInfos) ← PrettyPrinter.delabCore declaration.type {}
              PrettyPrinter.Delaborator.delab
            let type : TSyntax `term :=
              ⟨← freezeNormReplayReferences typeInfos explicitUniverses type.raw⟩
            return (← `(morew_replay_instance% $name : $type)).raw
          return name
      | _ => pure ()
  return stx.setArgs (← stx.getArgs.mapM (freezeNormReplayReferences infos explicitUniverses))

private def normReplaySyntax (expression : Expr)
    (explicitUniverses : Array (Expr × Lean.Syntax) := #[]) :
    TermElabM (Option Lean.Syntax) := do
  let expression ← instantiateMVars expression
  -- Keep this low-level syntax module independent of the normed-space library.
  unless (expression.find? (·.isAppOfArity `Norm.norm 3)).isSome do return none
  if expression.hasMVar then return none
  withOptions (fun options => options.set `pp.all true
      |>.set `pp.universes false
      |>.set `pp.explicit true |>.set `pp.instances true
      |>.set `pp.proofs true |>.set `pp.deepTerms true
      |>.set `pp.structureInstances false |>.set `pp.beta true
      |>.set `pp.coercions false |>.set `pp.maxSteps (1000000 : Nat)) do
    let (term, infos) ← PrettyPrinter.delabCore expression {}
      PrettyPrinter.Delaborator.delab
    return some (← freezeNormReplayReferences infos explicitUniverses term.raw)

-- Explicit universe arguments are not always inferable from the surrounding term.
-- Preserve explicit source arguments, including macro expansions, without
-- fixing inferred universes to the names of the source declaration's context.
private partial def explicitUniverseHead? (stx : Lean.Syntax) : Option Lean.Syntax :=
  if stx.isOfKind ``Lean.Parser.Term.explicitUniv then some stx
  else if stx.isOfKind ``Lean.Parser.Term.app then explicitUniverseHead? stx[0]
  else if stx.isOfKind ``Lean.Parser.Term.explicit || stx.isOfKind ``Lean.Parser.Term.paren then
    explicitUniverseHead? stx[1]
  else none

-- Applied constants have information on the head identifier but not always
-- on its universe suffix. Match that identifier's own information so a
-- coercion added around the application cannot receive the suffix instead.
private partial def explicitUniverseConstant? (head : Lean.Syntax) (tree : InfoTree) :
    TermElabM (Option Expr) := do
  match tree with
  | .context _ child => explicitUniverseConstant? head child
  | .node info children =>
      if let .ofTermInfo info := info then
        -- Name resolution can remove a quoted identifier's macro scopes in
        -- its own info node. Its source position and user spelling still
        -- identify the same head within this application's subtree.
        let sameHead := info.stx == head ||
          (info.stx.isIdent && head.isIdent && info.stx.getPos? == head.getPos? &&
            info.stx.getId.eraseMacroScopes == head.getId.eraseMacroScopes)
        if sameHead then
          let expression ← instantiateMVars info.expr
          if expression.isConst then return some expression
      for child in children do
        if let some expression ← explicitUniverseConstant? head child then return some expression
      return none
  | .hole _ => return none

private partial def collectExplicitNormUniverses (tree : InfoTree)
    (references : Array (Expr × Lean.Syntax) := #[]) :
    TermElabM (Array (Expr × Lean.Syntax)) := do
  match tree with
  | .context _ child => collectExplicitNormUniverses child references
  | .node info children =>
      let mut references := references
      if let .ofTermInfo info := info then
        if let some explicit := explicitUniverseHead? info.stx then
          if let some expression ← explicitUniverseConstant? explicit[0] tree then
            if let .const name _ := expression then
              let source := explicit.setArg 0 (mkCIdentFrom explicit[0] name)
              references := references.push (expression, source)
      for child in children do
        references ← collectExplicitNormUniverses child references
      return references
  | .hole _ => return references

private def inferredDefinitionTypes (definitions : List Morew.Syntax.DefinitionView)
    (body : Expr) : TermElabM (Array Morew.Syntax.DefinitionView) := do
  match definitions with
  | [] => pure #[]
  | definition :: remaining =>
      let .letE _ type value body _ := body.consumeMData
        | throwError "internal error: model-local definition spine was erased during elaboration"
      -- Inferred types have no original source node in the information tree.
      -- Preserve any instance-sensitive norm while the checked type is available.
      let typeSyntax ← match ← normReplaySyntax type with
        | some replay => pure replay
        | none => pure (← PrettyPrinter.delab type).raw
      let definition := { definition with
        inferredTypeSyntax? := some (← Morew.Syntax.preResolveTerm typeSyntax) }
      withLetDecl definition.name type value fun binding => do
        return #[definition] ++
          (← inferredDefinitionTypes remaining (body.instantiate1 binding))

private partial def collectNormReplays (fields : Array Lean.Syntax) (tree : InfoTree)
    (replays : Array (Lean.Syntax × Lean.Syntax)) :
    TermElabM (Array (Lean.Syntax × Lean.Syntax)) := do
  match tree with
  | .context _ child => collectNormReplays fields child replays
  | .node info children =>
      let mut replays := replays
      if let .ofTermInfo info := info then
        -- Serialize the whole source field. A macro can insert norms beneath
        -- lets, or splice one norm syntax into different instance contexts.
        -- Replacing individual syntax occurrences would lose those contexts.
        if fields.contains info.stx then
          let expression ← instantiateMVars info.expr
          if !expression.hasMVar && (expression.find? (·.isAppOfArity `Norm.norm 3)).isSome then
            let explicitUniverses ← collectExplicitNormUniverses tree
            if let some term ← withLCtx' info.lctx (normReplaySyntax expression explicitUniverses) then
              replays := replays.push (info.stx, term)
      for child in children do replays ← collectNormReplays fields child replays
      return replays
  | .hole _ => return replays

private def replaceNormReplay (replays : Array (Lean.Syntax × Lean.Syntax))
    (stx : Lean.Syntax) : Lean.Syntax :=
  match replays.find? (fun entry => entry.1 == stx) with
  | some (_, replay) => replay
  | none => stx

/-- Infer one shared local-definition environment before copying the checked
let spine into the objective and feasibility functions. -/
private def elaborateModelBody (view : Morew.Syntax.ProblemView)
    (productType objective feasible : TSyntax `term) (expectedType? : Option Expr) :
    TermElabM (Expr × Array Morew.Syntax.DefinitionView) := do
  let domain ← elabType productType
  let expectedProblem? : Option Expr ← expectedType?.mapM fun type => whnf type
  let expectedProblem? := expectedProblem?.filter (·.isAppOfArity ``Morew.Problem 2)
  if let some expected := expectedProblem? then
    unless ← isDefEq domain (expected.getArg! 0) do
      throwErrorAt productType
        "problem decision domain is{indentExpr domain}\nbut is expected to be{indentExpr (expected.getArg! 0)}"
  -- Share the domain's metavariables with the local decision binders. In
  -- particular, an inferred annotation must not be elaborated a second time.
  let types ← decisionTypes domain view.binders.size
  let declarations := view.binders.mapIdx fun index binder => (binder.name, types[index]!)
  let expectedValue? := expectedProblem?.map (·.getArg! 1)
  let expectedValue? := expectedValue?.map fun value =>
    if view.sense == .maximize && value.isAppOfArity ``OrderDual 1 then value.getArg! 0
    else value
  let pairType? ← expectedValue?.mapM fun value => mkAppM ``Prod #[value, mkSort Level.zero]
  withLocalDeclsDND declarations fun binders => do
    let pair ← `(($objective, ($feasible : Prop)))
    let pair ← liftMacroM <| view.wrapDefinitions pair
    let pair ← elabTerm pair pairType?
    synthesizeSyntheticMVarsNoPostponing
    let pair ← instantiateMVars pair
    let definitions ← inferredDefinitionTypes view.definitions.toList pair
    let (objective, feasible) ← splitModelPair pair
    -- The bodies can infer decision types even without an expected Problem
    -- type. Build checked projections only after those types are resolved.
    let domain ← instantiateMVars domain
    withLocalDeclD `point domain fun point => do
      let projections ← decisionProjections point view.binders.size
      let objective ← mkLambdaFVars #[point] (objective.replaceFVars binders projections)
      let feasible ← mkLambdaFVars #[point] (feasible.replaceFVars binders projections)
      let .forallE _ _ valueType _ ← whnf (← inferType objective)
        | throwError "internal error: model objective is not a function"
      let valueType ← match view.sense with
        | .minimize => pure valueType
        | .maximize => mkAppM ``OrderDual #[valueType]
      let result ← mkAppOptM ``Morew.Problem.mk
        #[some domain, some valueType, some objective, some feasible]
      let result ← elabTerm (← exprToSyntax result) expectedType?
      pure (result, definitions)

private def elaborateProblem (_stx : Lean.Syntax) (bindersStx : Array Lean.Syntax)
    (definitionsStx : Array Lean.Syntax)
    (sense : Morew.ObjectiveSense) (objective : TSyntax `term)
    (constraintsStx : Array Lean.Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let binderGroups ← liftMacroM <| bindersStx.mapM decodeBinder
  let binders := binderGroups.foldl (init := #[]) (fun result group => result ++ group)
  let constraints ← liftMacroM <| constraintsStx.mapM decodeConstraint
  let definitions ← liftMacroM <| definitionsStx.mapM decodeDefinition
  let binderRefs := bindersStx.flatMap fun ref =>
    match ref with
    | `(problemBinder| ($names:ident* : $_)) => names.map fun _ => ref
    | _ => #[]
  liftMacroM <| ensureDistinct "decision variable" (binders.map (fun binder => binder.name)) binderRefs
  liftMacroM <| ensureDistinct "constraint" (constraints.map (fun constraint => constraint.name)) constraintsStx
  liftMacroM <| ensureDistinct "model-local definition" (definitions.map (·.name)) definitionsStx
  for definition in definitions, ref in definitionsStx do
    if binders.any (fun binder => binder.name.eraseMacroScopes == definition.name.eraseMacroScopes) then
      throwErrorAt ref "model-local definition `{definition.name.eraseMacroScopes}` conflicts with a decision variable"
    if (← getLCtx).any (fun declaration =>
        !declaration.isImplementationDetail &&
          declaration.userName.eraseMacroScopes == definition.name.eraseMacroScopes) then
      throwErrorAt ref "model-local definition `{definition.name.eraseMacroScopes}` conflicts with an outer parameter"

  let binderNames : List (TSyntax `ident) := bindersStx.toList.flatMap fun binder =>
    match binder with
    | `(problemBinder| ($names:ident* : $_)) => names.toList
    | _ => []
  let binderTypes : List (TSyntax `term) := binders.toList.map fun
    (binder : Morew.Syntax.BinderView) => ⟨binder.typeSyntax⟩
  let constraintTerms : List (TSyntax `term) :=
    constraints.toList.map fun (constraint : Morew.Syntax.ConstraintView) => ⟨constraint.proposition⟩
  let productType ← liftMacroM <| mkProductType binderTypes
  let productPattern ← liftMacroM <| mkProductPattern binderNames
  let feasible ← liftMacroM <| mkConstraintConjunction constraintTerms
  let view : Morew.Syntax.ProblemView := { sense, binders, definitions, objective, constraints }
  let objectiveBody ← liftMacroM <| view.wrapDefinitions objective
  let feasibleBody ← liftMacroM <| view.wrapDefinitions feasible
  let resultSyntax ← match sense with
    | .minimize =>
        `(Morew.Problem.mk (X := $productType)
          (fun ($productPattern : $productType) => $objectiveBody)
          (fun ($productPattern : $productType) => $feasibleBody))
    | .maximize =>
        `(Morew.Problem.mk (X := $productType) (V := OrderDual _)
          (fun ($productPattern : $productType) => $objectiveBody)
          (fun ($productPattern : $productType) => $feasibleBody))
  let infoStart := (← getInfoTrees).size
  let (result, definitions) ← withEnableInfoTree true do
    let result ← if definitions.isEmpty then
        pure (← elabTerm resultSyntax expectedType?, definitions)
      else
        elaborateModelBody view productType objective feasible expectedType?
    synthesizeSyntheticMVars
    pure result
  if let some declName ← getDeclName? then
    let infoState ← getInfoState
    let fields := #[objective.raw] ++ binders.map (·.typeSyntax) ++
      constraints.map (·.proposition) ++ definitions.flatMap (fun definition =>
        #[definition.value] ++ definition.typeSyntax?.toArray ++
          definition.inferredTypeSyntax?.toArray)
    let mut normReplays := #[]
    for tree in infoState.trees.toArray[infoStart:] do
      normReplays ← collectNormReplays fields (tree.substitute infoState.assignment) normReplays
    let replayTerm (stx : Lean.Syntax) :=
      Morew.Syntax.preResolveTerm (replaceNormReplay normReplays stx)
    let replay : Morew.Syntax.ProblemView := {
      view with
      binders := ← binders.mapM fun binder => do
        pure { binder with typeSyntax := ← replayTerm binder.typeSyntax }
      definitions := ← definitions.mapM fun definition => do
        pure { definition with
          typeSyntax? := ← definition.typeSyntax?.mapM replayTerm
          inferredTypeSyntax? := ← definition.inferredTypeSyntax?.mapM replayTerm
          value := ← replayTerm definition.value }
      objective := ← replayTerm objective.raw
      constraints := ← constraints.mapM fun constraint => do
        pure { constraint with proposition := ← replayTerm constraint.proposition }
    }
    let binders ← binders.mapM fun binder => do
      pure { binder with typeSyntax := ← Morew.Syntax.preResolveTerm binder.typeSyntax }
    let objective ← Morew.Syntax.preResolveTerm objective.raw
    let definitions ← definitions.mapM fun definition => do
      pure { definition with
        typeSyntax? := ← definition.typeSyntax?.mapM Morew.Syntax.preResolveTerm
        inferredTypeSyntax? := ← definition.inferredTypeSyntax?.mapM Morew.Syntax.preResolveTerm
        value := ← Morew.Syntax.preResolveTerm definition.value }
    let constraints ← constraints.mapM fun constraint => do
      pure {
        constraint with
        proposition := ← Morew.Syntax.preResolveTerm constraint.proposition
      }
    Morew.Syntax.registerProblemView declName replay (some {
      sense
      binders
      definitions
      objective
      constraints
    })
  pure result

/-- Elaborate an unconstrained minimization problem term. -/
@[term_elab minimizeProblemTerm]
def elabProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* $definitions:problemDefinition* minimize $objective:term) =>
      elaborateProblem stx binders definitions .minimize objective #[] expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate a constrained minimization problem term. -/
@[term_elab minimizeConstrainedProblemTerm]
def elabConstrainedMinProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* $definitions:problemDefinition* minimize $objective:term
      subject to $constraints:problemConstraint*) =>
      elaborateProblem stx binders definitions .minimize objective constraints expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate an unconstrained maximization problem term. -/
@[term_elab maximizeProblemTerm]
def elabMaxProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* $definitions:problemDefinition* maximize $objective:term) =>
      elaborateProblem stx binders definitions .maximize objective #[] expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate a constrained maximization problem term. -/
@[term_elab maximizeConstrainedProblemTerm]
def elabConstrainedMaxProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* $definitions:problemDefinition* maximize $objective:term
      subject to $constraints:problemConstraint*) =>
      elaborateProblem stx binders definitions .maximize objective constraints expectedType?
  | _ => throwUnsupportedSyntax

end Morew
