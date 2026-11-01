/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Replace

/-!
# Derived constraints

Append a user-proved consequence of current feasibility. The supplied proof is
checked against the complete current semantic problem before the new row is
introduced. A fresh canonical checkpoint retains every displayed row and its
label across subsequent reformulations.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private partial def derivePointComponents (point : Expr) : Nat → MetaM (Array Expr)
  | 0 => pure #[]
  | 1 => pure #[point]
  | n + 2 => do
      let first ← mkAppM ``Prod.fst #[point]
      let last ← mkAppM ``Prod.snd #[point]
      return (← derivePointComponents first (n + 1)).push last

/-- Close the proposed row over exactly the current model bindings. -/
private def derivePredicate (state : ReformState)
    (typed : Morew.Elab.Reformulation.RunnerState) (proposition : TSyntax `term) :
    TermElabM (Expr × Syntax) :=
  withPresentationBinders typed.presentation fun _ binders =>
    withViewDefinitions state.view fun definitions => do
      let body ← elabPresentationTerm proposition (binders ++ definitions)
        (some (mkSort .zero))
      if (← getThe Core.State).messages.hasErrors then throwAbortTerm
      if body.hasMVar || body.hasSorry then
        throwErrorAt proposition "derived constraint contains unresolved metavariables or placeholders"
      unless ← isDefEq (← inferType body) (mkSort .zero) do
        throwErrorAt proposition "a derived constraint must be a proposition"
      let names := binders.mapIdx (fun i binding =>
        (binding.fvarId!, state.view.binders[i]!.name)) ++
        definitions.mapIdx (fun i binding =>
          (binding.fvarId!, state.view.definitions[i]!.name))
      let propositionSyntax ← delabPresentationTerm body names
      let body ← mkLetFVars definitions body (usedLetOnly := false)
      let predicate ← withLocalDeclD `point typed.semanticDomainType fun point => do
        let components ← derivePointComponents point binders.size
        mkLambdaFVars #[point] (body.replaceFVars binders components)
      return (predicate, propositionSyntax)

private def materializeDerive (state : ReformState) (label : TSyntax `ident)
    (proposition provided : TSyntax `term)
    (allocation : Morew.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some name := allocation.findName? 0
    | throwErrorAt label "internal error: missing derived constraint label allocation"
  runTermElabM fun sectionFVars => withoutErrToSorry do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let (predicate, propositionSyntax) ← derivePredicate state typed proposition
    -- The temporary model binders are no longer in scope: only the source
    -- point quantified by this contract may supply decision-dependent facts.
    let expected ← withLocalDeclD `point typed.semanticDomainType fun point => do
      let feasible ← mkAppM ``Morew.Problem.feasible #[typed.semantic, point]
      mkForallFVars #[point] (← mkArrow feasible (mkApp predicate point))
    let implied ← withRef provided do
      let proof ← elabTermEnsuringType provided expected
      synthesizeSyntheticMVarsNoPostponing
      if (← getThe Core.State).messages.hasErrors then throwAbortTerm
      let proof ← instantiateMVars proof
      if proof.hasMVar || proof.hasSorry then
        throwError "derived constraint proof contains unresolved metavariables or placeholders"
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        checkWithKernel proof
      pure proof
    let natural ← mkAppM ``Morew.Problem.addConstraint #[typed.semantic, predicate]
    let addition ← mkAppM ``Morew.addConstraintEquivalence
      #[typed.semantic, predicate, implied]
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
      Replace.storeCertificate `derivedConstraint primitive [
        (`derived_constraint, predicate), (`derived_source, typed.semantic),
        (`derived_target, next)]
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

/-- Preflight the explicit label before elaborating a derived row or its proof. -/
def prepareDerive (state : ReformState) (label : TSyntax `ident)
    (proposition provided : TSyntax `term) : CommandElabM SurfaceStepDraft :=
  pure {
    nameRequests := #[{
      id := 0, kind := .explicitConstraintLabel
      requested := label.getId.eraseMacroScopes, ref := label.raw }]
    materialize := materializeDerive state label proposition provided
  }

end Morew.Reformulation.Internal
