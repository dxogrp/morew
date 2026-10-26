/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Rewrite
import Morew.Reformulation.Conic

/-!
# Targeted exact smooth reformulations

`nlp at label` replaces a direct nonsmooth bound by exactly equivalent smooth
constraints. Native absolute value, positive part, maximum, finite supremum,
and one/infinity/Euclidean norms have upper-bound rules; minimum and finite
infimum have lower-bound rules. Operands and bounds may be nonlinear, provided
all replacement residuals can be certified C² on an open domain containing the
rewritten feasible set. This asserts no convexity.

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
nonterminal and emits no whole-model `NLP.Form`; bare `nlp` is a separate feature.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

private abbrev NLPPrepared := Morew.Elab.NLP.Rewrite.Result

private def nlpGeneratedStem (selector : TSyntax `ident) : CommandElabM String := do
  let .str _ stem := selector.getId.eraseMacroScopes
    | throwErrorAt selector "cannot derive a generated-name family from constraint `{selector.getId}`"
  if stem.isEmpty then
    throwErrorAt selector "cannot derive a generated-name family from an empty constraint label"
  return stem

private def materializeNLP (state : ReformState) (index : Nat)
    (prepared : NLPPrepared) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared := prepared.replaceFVars preparedVars sectionFVars
    let replacement ← Morew.Elab.Reformulation.Replace.rewriteConstraint typed.presentation index
      prepared.lift prepared.auxiliary? prepared.nextDomain prepared.rowPredicates prepared.targetIff
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
    let exact ← mkAppM ``Morew.GlobalEquivalence.trans
      #[typed.normalization.equivalence, replacement.equivalence]
    let primitive ← instantiateMVars (← state.runner.liftEquivalence exact)
    let predicates := typed.presentation.constraints.map (·.predicate) ++ prepared.rowPredicates
    let candidates := predicates.toList.zipIdx.map fun (predicate, index) =>
      (Name.mkSimple s!"nlp_row_{index}", predicate)
    let primitive ← shareConicCertificate primitive (candidates ++ [
      (`nlp_certificate, prepared.lift), (`nlp_source, typed.canonical),
      (`nlp_target, replacement.targetProblem)])
    checkWithKernel primitive
    let primitiveName ← mkAuxDeclName (kind := `_nlpCertificate)
    let primitive ← mkAuxDefinitionFor primitiveName primitive (zetaDelta := true)
      (compile := false)
    modifyEnv (addNoncomputable · primitiveName)
    let mut binders := state.view.binders
    if let some auxiliary := prepared.auxiliary? then
      let some name := allocation.findName? 0
        | throwError "internal error: missing NLP auxiliary allocation"
      let name ← withFreshMacroScope do MonadQuotation.addMacroScope name
      binders := binders.push { name, typeSyntax := ← presentationTypeSyntax auxiliary }
    let mut rows := #[]
    for i in [:prepared.rowPredicates.size] do
      let some name := allocation.findName? (i + 1)
        | throwError "internal error: missing NLP row allocation"
      rows := rows.push { name, proposition := (← `(True)).raw : Morew.Syntax.ConstraintView }
    let originalTypes := typed.presentation.binders.map (·.type)
    let binderTypes := match prepared.auxiliary? with
      | none => originalTypes
      | some auxiliary => originalTypes.push auxiliary
    let declarations := binders.mapIdx fun i binder => (binder.name, binderTypes[i]!)
    let renderedRows ← withLocalDeclsDND declarations fun decisions => do
      let point ← packPoint decisions
      let names := decisions.mapIdx fun i decision => (decision.fvarId!, binders[i]!.name)
      let context ← Simp.mkContext
        (simpTheorems := #[{}]) (congrTheorems := ← getSimpCongrTheorems)
      rows.mapIdxM fun i row => do
        let (body, _) ← dsimp (mkApp prepared.rowPredicates[i]! point) context
        pure { row with proposition := ← delabPresentationTerm body names }
    let view := {
      state.view with
      binders
      constraints := state.view.constraints.extract 0 index ++ renderedRows ++
        state.view.constraints.extract (index + 1) state.view.constraints.size
    }
    let semantic ← exactExpressionSyntax (← simpOnly replacement.targetProblem)
    return {
      view
      semantic
      semanticDomainType := ← exactExpressionSyntax prepared.nextDomain
      primitiveCertificate := ← exactExpressionSyntax primitive
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      removedConstraintNames := {}
      normalizationLemmas := state.normalizationLemmas
      checkpoint? := some { semantic, view }
      constraintSplices := #[{ index, count := rows.size }]
    }

/-- Certify a selected exact smooth replacement before allocating its names. -/
def prepareNLP (state : ReformState) (step : Syntax)
    (selector : TSyntax `ident) (rule? : Option (TSyntax `term)) :
    CommandElabM SurfaceStepDraft := withRef step do
  let some index := state.view.constraints.findIdx? fun constraint =>
      sameUserName constraint.name selector.getId
    | throwErrorAt selector "unknown or stale constraint label `{selector.getId.eraseMacroScopes}`"
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let rule? ← rule?.mapM fun ruleSyntax => do
      try
        let rule ← elabTerm ruleSyntax none
        synthesizeSyntheticMVarsNoPostponing
        let rule ← instantiateMVars rule
        if rule.hasMVar then throwError "exact rule contains unresolved metavariables"
        return rule
      catch
        | .error _ message =>
          throwErrorAt ruleSyntax
            "constraint `{selector.getId.eraseMacroScopes}`: failed to elaborate exact rule: {message}"
        | exception => throw exception
    let predicate := presentation.constraints[index]!.predicate
    let retained := presentation.constraints.extract 0 index ++
      presentation.constraints.extract (index + 1) presentation.constraints.size
    -- Only structural finite evidence is shared. The affine helper-expansion
    -- fallback is intentionally not part of smooth certification.
    let mut instances := #[]
    for source in #[presentation.objective] ++ presentation.constraints.map (·.predicate) do
      for inst in ← Morew.Elab.Affine.sourceFiniteInstances source do
        unless instances.contains inst do instances := instances.push inst
    let result ← Morew.Elab.Rewrite.Plan.withScopedFiniteInstances
      (fun result oldVars newVars => result.map
        (fun (value : NLPPrepared) => value.replaceFVars oldVars newVars)) instances.toList do
      Morew.Elab.NLP.Rewrite.plan predicate (retained.map (·.predicate)) rule? index
    match result with
    | .error error =>
      throwErrorAt selector "constraint `{selector.getId.eraseMacroScopes}`: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  let stem ← nlpGeneratedStem selector
  let mut nameRequests := #[]
  if prepared.auxiliary?.isSome then
    nameRequests := nameRequests.push {
      id := 0, kind := .generatedBinderFamily
      requested := Name.mkSimple (stem ++ "_aux"), ref := selector.raw
    }
  for i in [:prepared.rowPredicates.size] do
    nameRequests := nameRequests.push {
      id := i + 1, kind := .generatedRowFamily
      requested := Name.mkSimple s!"{stem}_nlp_{i + 1}", ref := selector.raw
    }
  return { nameRequests, materialize := materializeNLP state index prepared preparedVars }

end Morew.Reformulation.Internal
