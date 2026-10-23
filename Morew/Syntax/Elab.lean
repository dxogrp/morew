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

private def inferredDefinitionTypes (definitions : List Morew.Syntax.DefinitionView)
    (body : Expr) : TermElabM (Array Morew.Syntax.DefinitionView) := do
  match definitions with
  | [] => pure #[]
  | definition :: remaining =>
      let .letE _ type value body _ := body.consumeMData
        | throwError "internal error: model-local definition spine was erased during elaboration"
      let typeSyntax ← PrettyPrinter.delab type
      let definition := { definition with
        inferredTypeSyntax? := some (← Morew.Syntax.preResolveTerm typeSyntax.raw) }
      withLetDecl definition.name type value fun binding => do
        return #[definition] ++
          (← inferredDefinitionTypes remaining (body.instantiate1 binding))

/-- Infer one shared local-definition environment before copying the checked
let spine into the objective and feasibility functions. -/
private def elaborateModelBody (view : Morew.Syntax.ProblemView)
    (productType objective feasible : TSyntax `term) (expectedType? : Option Expr) :
    TermElabM (Expr × Array Morew.Syntax.DefinitionView) := do
  let domain ← elabType productType
  let types ← view.binders.mapM fun binder => elabType binder.typeSyntax
  let declarations := view.binders.mapIdx fun index binder => (binder.name, types[index]!)
  let expectedValue? : Option Expr ← expectedType?.mapM fun type => whnf type
  let expectedValue? := expectedValue?.bind fun expected =>
    if expected.isAppOfArity ``Morew.Problem 2 then some (expected.getArg! 1) else none
  let expectedValue? := expectedValue?.map fun value =>
    if view.sense == .maximize && value.isAppOfArity ``OrderDual 1 then value.getArg! 0
    else value
  let pairType? ← expectedValue?.mapM fun value => mkAppM ``Prod #[value, mkSort Level.zero]
  withLocalDeclD `point domain fun point => do
    let projections ← decisionProjections point view.binders.size
    withLocalDeclsDND declarations fun binders => do
      let pair ← `(($objective, ($feasible : Prop)))
      let pair ← liftMacroM <| view.wrapDefinitions pair
      let pair ← elabTerm pair pairType?
      synthesizeSyntheticMVarsNoPostponing
      let pair ← instantiateMVars pair
      let definitions ← inferredDefinitionTypes view.definitions.toList pair
      let (objective, feasible) ← splitModelPair pair
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
        `(Morew.Problem.mk
          (fun ($productPattern : $productType) => $objectiveBody)
          (fun ($productPattern : $productType) => $feasibleBody))
    | .maximize =>
        `(Morew.Problem.mk (V := OrderDual _)
          (fun ($productPattern : $productType) => $objectiveBody)
          (fun ($productPattern : $productType) => $feasibleBody))
  let (result, definitions) ← if definitions.isEmpty then
      pure (← elabTerm resultSyntax expectedType?, definitions)
    else
      elaborateModelBody view productType objective feasible expectedType?
  if let some declName ← getDeclName? then
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
    Morew.Syntax.registerProblemView declName {
      sense
      binders
      definitions
      objective
      constraints
    }
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
