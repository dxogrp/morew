/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Replace

/-!
# Appending certified constraints

Derived constraints and certified restrictions share typed row elaboration and
canonical presentation. Their handlers check different semantic certificates;
this module only closes the new predicate and appends the certified row.
-/

namespace Morew.Reformulation.Internal.Append

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

/-- Diagnostics and stored-certificate names for a constraint-adding step. -/
structure Style where
  /-- Description used when elaborating the proposed predicate. -/
  description : String
  /-- Kind of the auxiliary declaration storing the primitive certificate. -/
  certificateKind : Name
  /-- Prefix of shared expressions within the stored certificate. -/
  family : String

private partial def pointComponents (point : Expr) : Nat → MetaM (Array Expr)
  | 0 => pure #[]
  | 1 => pure #[point]
  | n + 2 => do
      let first ← mkAppM ``Prod.fst #[point]
      let last ← mkAppM ``Prod.snd #[point]
      return (← pointComponents first (n + 1)).push last

/-- Close the proposed row over exactly the current model bindings. The caller
checks its semantic certificate after these temporary bindings leave scope. -/
def elaboratePredicate (style : Style) (state : ReformState)
    (typed : Morew.Elab.Reformulation.RunnerState) (proposition : TSyntax `term) :
    TermElabM (Expr × Syntax) :=
  withPresentationBinders typed.presentation fun _ binders =>
    withViewDefinitions state.view fun definitions => do
      let body ← elabPresentationTerm proposition (binders ++ definitions)
        (some (mkSort .zero))
      if (← getThe Core.State).messages.hasErrors then throwAbortTerm
      if body.hasMVar || body.hasSorry then
        throwErrorAt proposition
          "{style.description} contains unresolved metavariables or placeholders"
      unless ← isDefEq (← inferType body) (mkSort .zero) do
        throwErrorAt proposition "a {style.description} must be a proposition"
      let names := binders.mapIdx (fun i binding =>
        (binding.fvarId!, state.view.binders[i]!.name)) ++
        definitions.mapIdx (fun i binding =>
          (binding.fvarId!, state.view.definitions[i]!.name))
      let propositionSyntax ← delabPresentationTerm body names
      let body ← mkLetFVars definitions body (usedLetOnly := false)
      let predicate ← withLocalDeclD `point typed.semanticDomainType fun point => do
        let components ← pointComponents point binders.size
        mkLambdaFVars #[point] (body.replaceFVars binders components)
      return (predicate, propositionSyntax)

/-- Append one certified row, normalizing only its conjunction with the current
presentation. A new checkpoint protects existing row boundaries and labels. -/
def finish (style : Style) (state : ReformState)
    (typed : Morew.Elab.Reformulation.RunnerState) (name : Name)
    (proposition : TSyntax `term) (predicate : Expr) (propositionSyntax : Syntax)
    (addition : Expr) : TermElabM SurfaceStepResult := do
  let natural ← mkAppM ``Morew.Problem.addConstraint #[typed.semantic, predicate]
  let presentation := { typed.presentation with
    constraints := typed.presentation.constraints.push {
      name, predicate, ref := proposition.raw } }
  let next ← presentation.canonicalProblem
  let feasibleIff ← withLocalDeclD `point typed.semanticDomainType fun point => do
    let unchanged ← mkAppM ``Iff.refl #[mkApp predicate point]
    let normalized ← mkAppM ``and_congr
      #[mkApp typed.normalization.feasibleIff point, unchanged]
    let currentFeasible ← mkAppM ``Morew.Problem.feasible #[typed.canonical, point]
    let nextFeasible ← mkAppM ``Morew.Problem.feasible #[next, point]
    let appended := mkApp2 (mkConst ``And) currentFeasible (mkApp predicate point)
    let reassociationType := mkApp2 (mkConst ``Iff) appended nextFeasible
    let reassociation ← elabTermEnsuringType
      (← `(by simp only [and_assoc, true_and])) reassociationType
    synthesizeSyntheticMVarsNoPostponing
    let reassociation ← instantiateMVars reassociation
    mkLambdaFVars #[point] (← mkAppM ``Iff.trans #[normalized, reassociation])
  let normalization ← mkAppM ``Morew.pointwiseEquivalence
    #[natural, next, typed.normalization.objectiveEquality, feasibleIff]
  let exact ← mkAppM ``Morew.GlobalEquivalence.trans #[addition, normalization]
  let primitive ← state.runner.liftEquivalence exact
  let primitive ← withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
    Replace.storeCertificate style.certificateKind primitive [
      (Name.mkSimple (style.family ++ "_constraint"), predicate),
      (Name.mkSimple (style.family ++ "_source"), typed.semantic),
      (Name.mkSimple (style.family ++ "_target"), next)]
  let view := { state.view with
    constraints := state.view.constraints.push { name, proposition := propositionSyntax } }
  let semantic ← exactExpressionSyntax next
  return {
    view
    semantic
    semanticDomainType := state.semanticDomainType
    primitiveCertificate := ← exactExpressionSyntax primitive
    simplifyExpLogTerms := state.simplifyExpLogTerms
    hasSubstitution := state.hasSubstitution
    removedConstraintNames := {}
    normalizationLemmas := state.normalizationLemmas
    checkpoint? := some { semantic, view }
  }

end Morew.Reformulation.Internal.Append
