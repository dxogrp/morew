/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.NLP.Rewrite
import Morew.Elab.Reformulation.Rows
import Morew.Elab.Expr

/-! Replace a selected bound with equivalent smooth constraints. Discovery requires
one certified `morew_nlp` rule; `using` selects a single declaration or certificate.
Rules match the whole selected predicate.

Prove exactness from retained constraints, then use generated guards to certify residuals
on an open domain containing the new feasible set. Vector and finite-family rows stay
grouped. Replace the selected label with fresh `_nlp_i` row names and `_aux` binders;
further steps may follow. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def nlpStyle : Rows.Style := {
  family := "nlp", diagnostic := "NLP", certificateKind := `_nlpCertificate
}

private def materializeNLP (state : ReformState) (index : Nat)
    (prepared : Morew.Elab.NLP.Rewrite.Result) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared := prepared.replaceFVars preparedVars sectionFVars
    let replacement ← Morew.Elab.Reformulation.Replace.applyReplacement
      typed.presentation index prepared.toResult
    -- Require analytic evidence for this ordered replacement and proposed feasibility.
    let feasible ← mkAppM ``Morew.Problem.feasible #[replacement.targetProblem]
    let expected ← withLocalDeclD `point prepared.nextDomain fun point => do
      let membership ← mkAppM ``Membership.mem #[prepared.certified.domain, point]
      mkForallFVars #[point] (← mkArrow (mkApp feasible point) membership)
    unless ← isDefEq (← inferType prepared.certified.feasibleMemDomain) expected do
      throwError "internal error: smooth domain does not cover the rewritten feasibility predicate"
    for proof in prepared.certified.rowCertificates ++
        #[prepared.certified.domainIsOpen, prepared.certified.feasibleMemDomain] do
      checkWithKernel proof
    Rows.finish nlpStyle state typed index {
      auxiliary? := prepared.auxiliary?
      nextDomain := prepared.nextDomain
      rowPredicates := prepared.rowPredicates
      «certificate» := prepared.certificate.expression
      replacement
    } allocation

/-- Certify a selected exact smooth replacement before allocating its names. -/
def prepareNLP (state : ReformState) (step : Syntax)
    (selector : TSyntax `ident) (rule? : Option (TSyntax `term)) :
    CommandElabM SurfaceStepDraft := withRef step do
  let index ← Rows.findConstraint state selector
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let (rule?, declaration?) ← Rows.elaborateRule selector rule?
    let predicate := presentation.constraints[index]!.predicate
    let retained := splice presentation.constraints index #[]
    -- Share structural finite evidence without affine helper expansion.
    let mut instances := #[]
    for source in #[presentation.objective] ++ presentation.constraints.map (·.predicate) do
      for inst in ← Morew.Elab.Expr.sourceFiniteInstances source do
        unless instances.contains inst do instances := instances.push inst
    let result ← Morew.Elab.Rewrite.Plan.withScopedFiniteInstances
      (fun result oldVars newVars => result.map
        (fun (value : Morew.Elab.NLP.Rewrite.Result) =>
          value.replaceFVars oldVars newVars)) instances.toList do
      Morew.Elab.NLP.Rewrite.plan predicate (retained.map (·.predicate)) rule? index declaration?
    match result with
    | .error error =>
      throwErrorAt selector "constraint `{selector.getId.eraseMacroScopes}`: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  return {
    nameRequests := ← Rows.nameRequests nlpStyle selector
      prepared.auxiliary?.isSome prepared.rowPredicates.size
    materialize := materializeNLP state index prepared preparedVars
  }

@[morew_reformulation_step Morew.nlpAtStep]
private def elabNLPAt : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| nlp at $selector:ident $[using $rule:term]?) =>
      prepareNLP state step selector rule
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
