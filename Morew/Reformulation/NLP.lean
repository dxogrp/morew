/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Rewrite
import Morew.Reformulation.Replace
import Morew.Elab.Expr

/-!
# Targeted exact smooth reformulations

`nlp at label` replaces a direct nonsmooth bound by exactly equivalent smooth
constraints. Native absolute value, positive part, maximum, finite supremum,
and one/infinity/Euclidean norms have upper-bound rules; minimum and finite
infimum have lower-bound rules. Operands and bounds may be nonlinear, provided
all replacement residuals can be certified C² on an open domain containing the
rewritten feasible set. This asserts no convexity.

Automatic rewriting discovers `@[morew_nlp]` declarations and requires exactly
one fully certified result. Shipped and user-defined rules use the same path;
ambiguous successes are listed by fully qualified name. `using ruleName`
selects only that declaration, inferring its parameters from the row. It need
not be registered. Applied certificate expressions retain ordinary Lean
elaboration, and an explicit failure never triggers automatic fallback.

The command handles one outer operation. Use an occurrence epigraph or hypograph
step first to expose a nested operation. `using rule` supplies an exact-lift,
graph, epigraph, or hypograph representation of the entire selected predicate;
it does not register a rule or bypass smoothness and domain certification.

Coordinate inequalities and finite families remain grouped, including symbolic
dimensions. The selected label is consumed. Generated labels use its final
component followed by `_nlp_1`, `_nlp_2`, and so on; auxiliaries use `_aux`.
The shared allocator freshens collisions without changing untouched labels.

Domain evidence comes from checked closed comparisons in the proposed target,
including generated guards, after exactness has been proved independently.
Unsupported retained rows and the objective remain untouched. This step is
nonterminal and emits no whole-model `NLP.Form`. Bare `nlp` performs terminal
whole-model validation and emits a concrete form and representability proof.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

private abbrev NLPPrepared := Morew.Elab.NLP.Rewrite.Result

private def nlpStyle : Replace.Style := {
  family := "nlp", diagnostic := "NLP", certificateKind := `_nlpCertificate
}

private def materializeNLP (state : ReformState) (index : Nat)
    (prepared : NLPPrepared) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared := prepared.replaceFVars preparedVars sectionFVars
    let replacement ← Morew.Elab.Reformulation.Replace.applyReplacement
      typed.presentation index prepared.toResult
    -- The analytic evidence must cover this precise ordered replacement, not
    -- a stronger predicate or merely the selected row's original domain.
    let feasible ← mkAppM ``Morew.Problem.feasible #[replacement.targetProblem]
    let expected ← withLocalDeclD `point prepared.nextDomain fun point => do
      let membership ← mkAppM ``Membership.mem #[prepared.certified.domain, point]
      mkForallFVars #[point] (← mkArrow (mkApp feasible point) membership)
    unless ← isDefEq (← inferType prepared.certified.feasibleMemDomain) expected do
      throwError "internal error: smooth domain does not cover the rewritten feasibility predicate"
    for proof in prepared.certified.rowCertificates ++
        #[prepared.certified.domainIsOpen, prepared.certified.feasibleMemDomain] do
      checkWithKernel proof
    Replace.finish nlpStyle state typed index {
      auxiliary? := prepared.auxiliary?
      nextDomain := prepared.nextDomain
      rowPredicates := prepared.rowPredicates
      certificate := prepared.certificate.expression
      replacement
    } allocation

/-- Certify a selected exact smooth replacement before allocating its names. -/
def prepareNLP (state : ReformState) (step : Syntax)
    (selector : TSyntax `ident) (rule? : Option (TSyntax `term)) :
    CommandElabM SurfaceStepDraft := withRef step do
  let index ← Replace.findConstraint state selector
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let (rule?, declaration?) ← Replace.elaborateRule selector rule?
    let predicate := presentation.constraints[index]!.predicate
    let retained := presentation.constraints.extract 0 index ++
      presentation.constraints.extract (index + 1) presentation.constraints.size
    -- Only structural finite evidence is shared. The affine helper-expansion
    -- fallback is intentionally not part of smooth certification.
    let mut instances := #[]
    for source in #[presentation.objective] ++ presentation.constraints.map (·.predicate) do
      for inst in ← Morew.Elab.Expr.sourceFiniteInstances source do
        unless instances.contains inst do instances := instances.push inst
    let result ← Morew.Elab.Rewrite.Plan.withScopedFiniteInstances
      (fun result oldVars newVars => result.map
        (fun (value : NLPPrepared) => value.replaceFVars oldVars newVars)) instances.toList do
      Morew.Elab.NLP.Rewrite.plan predicate (retained.map (·.predicate)) rule? index declaration?
    match result with
    | .error error =>
      throwErrorAt selector "constraint `{selector.getId.eraseMacroScopes}`: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  return {
    nameRequests := ← Replace.nameRequests nlpStyle selector
      prepared.auxiliary?.isSome prepared.rowPredicates.size
    materialize := materializeNLP state index prepared preparedVars
  }

end Morew.Reformulation.Internal
