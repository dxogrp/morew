/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Terminal
import Morew.Reformulation.Replace

/-!
# Terminal smooth-NLP validation

Bare `nlp` certifies the complete objective and constraints on one common open
evaluation domain after applying supported exact rewrites to direct nonsmooth
bounds. It emits the unchanged objective and comparison presentation together
with `.nlpForm` and `.isSmoothNLP`; no evaluation-domain guard is added to the
feasible predicate. The concrete form alone flattens comparisons and finite
coordinate families into scalar residuals and closed bounds.

For `reformulation ready : source := by nlp`, the declarations include
`ready.equivalence : GlobalEquivalence source ready`, `ready.nlpForm : NLP.Form ready`,
and `ready.isSmoothNLP : IsSmoothNLP ready`. The form's
`ready.nlpForm.represents : ready.nlpForm.data.toProblem = ready` includes objective
values outside the evaluation domain. Its rows alone define feasibility.

Scalar comparisons store the unchanged difference `a - b`: `a ≤ b` has upper
bound zero, `a ≥ b` has lower bound zero, and `a = b` is fixed at zero. Named
conjunction groups and `True` stay in the displayed target. Finite-vector
comparisons and nested `Fin n` families flatten only inside the form, including
symbolic and zero dimensions. General quantifiers are unsupported.

This terminal step asserts smoothness, not convexity, and accepts nonconvex
polynomials and products. It preserves maximizing objectives with an explicit
`OrderDual ℝ` value type and separately records `.maximize` in the form. Use
occurrence lifting or `nlp at label` before terminal validation when a nested
nonsmooth expression needs explicit preparation. Subsequent steps in the same
script are rejected; the emitted problem can start a new reformulation.

All generated names are allocated together. Form checking, declaration emission,
and presentation registration share the reformulation command's transaction.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

private def terminalNLPStem (state : ReformState) (origin : Nat) : CommandElabM String := do
  let name := state.view.constraints[origin]!.name.eraseMacroScopes
  let .str _ stem := name
    | throwError "cannot derive a generated-name family from constraint `{name}`"
  return stem

private def materializeTerminalNLP (state : ReformState)
    (prepared : Morew.Elab.NLP.Terminal.Result) (preparedVars : Array Expr)
    (allocation : NameAllocation) : CommandElabM SurfaceStepResult :=
  runTermElabM fun sectionFVars => do
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let prepared := prepared.replaceFVars preparedVars sectionFVars
    let targetProblem ← prepared.presentation.canonicalProblem
    let exact ← mkAppM ``Morew.GlobalEquivalence.trans
      #[typed.normalization.equivalence, prepared.equivalence]
    let primitive ← state.runner.liftEquivalence exact
    let candidates := (typed.presentation.constraints ++ prepared.presentation.constraints).toList
      |>.zipIdx |>.map fun (row, index) => (Name.mkSimple s!"terminal_row_{index}", row.predicate)
    let primitive ← Replace.storeCertificate `_terminalNLPCertificate primitive
      (candidates ++ [(`terminal_source, typed.canonical), (`terminal_target, targetProblem)])
    let mut binders := state.view.binders
    for i in [:prepared.auxiliaries.size] do
      let some name := allocation.findName? i
        | throwError "internal error: missing terminal NLP auxiliary allocation"
      let name ← withFreshMacroScope do MonadQuotation.addMacroScope name
      binders := binders.push {
        name
        typeSyntax := ← presentationTypeSyntax prepared.auxiliaries[i]!.2
      }
    let mut rows := #[]
    for i in [:prepared.rowOrigins.size] do
      let origin := prepared.rowOrigins[i]!
      if prepared.replacedIndices.contains origin then
        let some name := allocation.findName? (prepared.auxiliaries.size + i)
          | throwError "internal error: missing terminal NLP row allocation"
        rows := rows.push { name, proposition := (← `(True)).raw : Morew.Syntax.ConstraintView }
      else
        rows := rows.push state.view.constraints[origin]!
    let template := { state.view with binders, constraints := rows }
    let rendered ← problemViewFromExpression targetProblem template (recoverDefinitions := false)
    -- Retained syntax preserves exact binding identities. Generated rows use
    -- the planner's actual expressions rather than inferred alias references.
    let constraints := template.constraints.mapIdx fun i row =>
      if prepared.replacedIndices.contains prepared.rowOrigins[i]! then
        rendered.constraints[i]!
      else row
    let view := { template with constraints }
    let semantic ← exactExpressionSyntax targetProblem
    let formName ← mkAuxDeclName (kind := `_terminalNLPForm)
    let form ← mkAuxDefinitionFor formName prepared.form (zetaDelta := true) (compile := false)
    modifyEnv (addNoncomputable · formName)
    return {
      view
      semantic
      semanticDomainType := ← exactExpressionSyntax prepared.presentation.domainType
      primitiveCertificate := ← exactExpressionSyntax primitive
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      removedConstraintNames := {}
      normalizationLemmas := state.normalizationLemmas
      checkpoint? := some { semantic, view }
      constraintSplices := prepared.replacedIndices.map fun index =>
        { index, count := (prepared.rowOrigins.filter (· == index)).size }
      terminalForm? := some (.nlp, ← exactExpressionSyntax form)
      status := .terminal
    }

/-- Certify the whole smooth problem and request all generated local names. -/
def prepareTerminalNLP (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft := withRef step do
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    match ← Morew.Elab.NLP.Terminal.plan presentation with
    | .error error => throwError error.reason
    | .ok result => pure (result, sectionFVars)
  let mut nameRequests := #[]
  for i in [:prepared.auxiliaries.size] do
    let stem ← terminalNLPStem state prepared.auxiliaries[i]!.1
    nameRequests := nameRequests.push {
      id := i, kind := .generatedBinderFamily
      requested := Name.mkSimple (stem ++ "_aux"), ref := step }
  let mut counts := Array.replicate state.view.constraints.size 0
  for i in [:prepared.rowOrigins.size] do
    let origin := prepared.rowOrigins[i]!
    if prepared.replacedIndices.contains origin then
      let count := counts[origin]! + 1
      counts := counts.set! origin count
      let stem ← terminalNLPStem state origin
      nameRequests := nameRequests.push {
        id := prepared.auxiliaries.size + i, kind := .generatedRowFamily
        requested := Name.mkSimple s!"{stem}_nlp_{count}", ref := step }
  return { nameRequests, materialize := materializeTerminalNLP state prepared preparedVars }

end Morew.Reformulation.Internal
