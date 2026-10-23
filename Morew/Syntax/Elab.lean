import Morew.Syntax.Presentation

/-!
# Problem term elaboration

Elaborate minimization and maximization terms into semantic problems and
register their source presentations. Public elaborator names remain in `Morew`.
-/

namespace Morew

open Lean Lean.Elab Lean.Elab.Term Lean.Parser

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

private def elaborateProblem (_stx : Lean.Syntax) (bindersStx : Array Lean.Syntax)
    (sense : Morew.ObjectiveSense) (objective : TSyntax `term)
    (constraintsStx : Array Lean.Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let binderGroups ← liftMacroM <| bindersStx.mapM decodeBinder
  let binders := binderGroups.foldl (init := #[]) (fun result group => result ++ group)
  let constraints ← liftMacroM <| constraintsStx.mapM decodeConstraint
  let binderRefs := bindersStx.flatMap fun ref =>
    match ref with
    | `(problemBinder| ($names:ident* : $_)) => names.map fun _ => ref
    | _ => #[]
  liftMacroM <| ensureDistinct "decision variable" (binders.map (fun binder => binder.name)) binderRefs
  liftMacroM <| ensureDistinct "constraint" (constraints.map (fun constraint => constraint.name)) constraintsStx

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
  let resultSyntax ← match sense with
    | .minimize =>
        `(Morew.Problem.mk
          (fun ($productPattern : $productType) => $objective)
          (fun ($productPattern : $productType) => $feasible))
    | .maximize =>
        `(Morew.Problem.mk (V := OrderDual _)
          (fun ($productPattern : $productType) => $objective)
          (fun ($productPattern : $productType) => $feasible))
  let result ← elabTerm resultSyntax expectedType?
  if let some declName ← getDeclName? then
    let binders ← binders.mapM fun binder => do
      pure { binder with typeSyntax := ← Morew.Syntax.preResolveTerm binder.typeSyntax }
    let objective ← Morew.Syntax.preResolveTerm objective.raw
    let constraints ← constraints.mapM fun constraint => do
      pure {
        constraint with
        proposition := ← Morew.Syntax.preResolveTerm constraint.proposition
      }
    Morew.Syntax.registerProblemView declName {
      sense
      binders
      objective
      constraints
    }
  pure result

/-- Elaborate an unconstrained minimization problem term. -/
@[term_elab minimizeProblemTerm]
def elabProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* minimize $objective:term) =>
      elaborateProblem stx binders .minimize objective #[] expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate a constrained minimization problem term. -/
@[term_elab minimizeConstrainedProblemTerm]
def elabConstrainedMinProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* minimize $objective:term
      subject to $constraints:problemConstraint*) =>
      elaborateProblem stx binders .minimize objective constraints expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate an unconstrained maximization problem term. -/
@[term_elab maximizeProblemTerm]
def elabMaxProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* maximize $objective:term) =>
      elaborateProblem stx binders .maximize objective #[] expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate a constrained maximization problem term. -/
@[term_elab maximizeConstrainedProblemTerm]
def elabConstrainedMaxProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* maximize $objective:term
      subject to $constraints:problemConstraint*) =>
      elaborateProblem stx binders .maximize objective constraints expectedType?
  | _ => throwUnsupportedSyntax

end Morew
