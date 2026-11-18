/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Elab.Reformulation.Registry
public import Morew.Elab.Cone.Rewrite
public import Morew.Elab.Reformulation.Rows
public import Morew.Elab.Expr

/-! Replace the constraint selected by `conic at label` with an exact conic representation.
Discovery requires one certified `morew_conic` rule after the built-in rule preferences;
`using` selects a single declaration or certificate.

Generated rows require affine coordinates and cone certificates, including global
symmetry for PSD rows. Domain premises use independent hypotheses or retained constraints;
replacement predicates are independent of temporary feasibility proofs. Finite sets
and exponents require independent evidence.

Replace the selected label with fresh `_conic_i` row names and `_aux` binders.
Vector rows and finite cone families remain grouped; further steps may follow. -/

public meta section

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def conicStyle : Rows.Style := {
  family := "conic", diagnostic := "conic", certificateKind := `_conicCertificate
}

private def materializeConic (state : ReformState) (index : Nat)
    (prepared : Morew.Elab.Cone.Plan.Result) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    -- Instantiate section-local types before kernel checking.
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared : Morew.Elab.Cone.Plan.Result :=
      Morew.Elab.Cone.Plan.Result.replaceFVars prepared preparedVars sectionFVars
    let replacement ← Morew.Elab.Reformulation.Replace.applyReplacement
      typed.presentation index prepared.toResult
    Rows.finish conicStyle state typed index {
      auxiliary? := prepared.auxiliary?
      nextDomain := prepared.nextDomain
      rowPredicates := prepared.rowPredicates
      «certificate» := prepared.certificate.expression
      replacement
    } allocation

/-- Certify the selected constraint before allocating its names and constructing its replacement. -/
def prepareConic (state : ReformState) (step : Syntax)
    (selector : TSyntax `ident) (rule? : Option (TSyntax `term)) :
    CommandElabM SurfaceStepDraft := withRef step do
  let index ← Rows.findConstraint state selector
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let (rule?, declaration?) ← Rows.elaborateRule selector rule?
    let predicate := presentation.constraints[index]!.predicate
    let result : Except Morew.Elab.Expr.Error Morew.Elab.Cone.Plan.Result ←
      Morew.Elab.Cone.Finite.withPresentationFiniteInstances
        Morew.Elab.Cone.Plan.Result.replaceFVars presentation do
        let retained := splice presentation.constraints index #[]
        if let some name := declaration? then do
          Morew.Elab.Cone.Rewrite.planDeclaration predicate name (retained.map (·.predicate))
        else if let some rule := rule? then do
          Morew.Elab.Cone.Rewrite.planExplicit predicate rule (retained.map (·.predicate))
        else do
          Morew.Elab.Cone.Rewrite.planUnique predicate (retained.map (·.predicate))
    match result with
    | .error error =>
      throwErrorAt selector "constraint `{selector.getId.eraseMacroScopes}`: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  return {
    nameRequests := ← Rows.nameRequests conicStyle selector
      prepared.auxiliary?.isSome prepared.rowPredicates.size
    materialize := materializeConic state index prepared preparedVars
  }

/-- Elaborate a certified conic rewrite of one selected constraint. -/
@[morew_reformulation_step Morew.conicAtStep]
def elabConicAt : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| conic at $selector:ident $[using $rule:term]?) =>
      prepareConic state step selector rule
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
