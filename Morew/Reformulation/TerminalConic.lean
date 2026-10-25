/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Terminal
import Morew.Reformulation.Conic

/-!
# Terminal cone-membership conversion

Bare `conic` lowers nonlinear conjunction leaves exactly and converts affine
comparisons to nonnegative- or zero-cone memberships. Named affine groups and
their local-definition references are preserved. The checked structural form
is emitted beside the normalized target. All generated local names are
allocated together before the terminal result is materialized.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

private def terminalStem (state : ReformState) (origin : Nat) : CommandElabM String := do
  let name := state.view.constraints[origin]!.name.eraseMacroScopes
  let .str _ stem := name
    | throwError "cannot derive a generated-name family from constraint `{name}`"
  return stem

-- Retained source entries carry binding identities that the canonical semantic
-- predicates may have reduced away. Normalize them in their original local-let
-- scope; generated entries instead use the checked planner's actual expressions.
-- Target emission subsequently checks this complete view against the canonical
-- problem, including any identities established by preceding substitutions.
private def normalizeRetainedView (prepared : Morew.Elab.Conic.Terminal.Result)
    (template rendered : Morew.Syntax.ProblemView) : TermElabM Morew.Syntax.ProblemView := do
  let declarations := template.binders.mapIdx fun i binder =>
    (binder.name, prepared.presentation.binders[i]!.type)
  withLocalDeclsDND declarations fun decisions =>
    withViewDefinitions template fun definitions => do
      let bindings := decisions ++ definitions
      let names := bindings.mapIdx fun i binding =>
        (binding.fvarId!, if i < decisions.size then template.binders[i]!.name
          else template.definitions[i - decisions.size]!.name)
      let constraints ← template.constraints.mapIdxM fun i row => do
        let origin := prepared.rowOrigins[i]!
        if prepared.replacedIndices.contains origin then
          return rendered.constraints[i]!
        unless prepared.changedBodies.contains origin do return row
        let body ← elabPresentationTerm ⟨row.proposition⟩ bindings (some (mkSort .zero))
        synthesizeSyntheticMVarsNoPostponing
        let body ← instantiateMVars body
        let normalized ← Morew.Elab.Conic.normalizeBody body
        checkWithKernel normalized.iff
        return { row with proposition := ← delabPresentationTerm normalized.body names }
      return { template with constraints }

private def materializeTerminalConic (state : ReformState)
    (prepared : Morew.Elab.Conic.Terminal.Result) (preparedVars : Array Expr)
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
    let primitive ← shareConicCertificate (← instantiateMVars primitive)
      (candidates ++ [(`terminal_source, typed.canonical), (`terminal_target, targetProblem)])
    checkWithKernel primitive
    let primitiveName ← mkAuxDeclName (kind := `_terminalConicCertificate)
    let primitive ← mkAuxDefinitionFor primitiveName primitive (zetaDelta := true)
      (compile := false)
    modifyEnv (addNoncomputable · primitiveName)
    let mut binders := state.view.binders
    for i in [:prepared.auxiliaries.size] do
      let some name := allocation.findName? i
        | throwError "internal error: missing terminal auxiliary allocation"
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
          | throwError "internal error: missing terminal row allocation"
        rows := rows.push { name, proposition := (← `(True)).raw : Morew.Syntax.ConstraintView }
      else
        rows := rows.push state.view.constraints[origin]!
    let template := { state.view with binders, constraints := rows }
    let rendered ← problemViewFromExpression targetProblem template (recoverDefinitions := false)
    let view ← normalizeRetainedView prepared template rendered
    let semantic ← exactExpressionSyntax targetProblem
    let formName ← mkAuxDeclName (kind := `_terminalConicForm)
    let form ← mkAuxDefinitionFor formName prepared.form (zetaDelta := true) (compile := false)
    modifyEnv (addNoncomputable · formName)
    -- Canonical predicates may have reduced a zero-valued model definition,
    -- while the retained view deliberately still refers to its binding. These
    -- equalities check their agreement without rewriting the displayed body.
    let normalizationLemmas := state.normalizationLemmas ++
      #[⟨mkCIdent ``sub_zero⟩, ⟨mkCIdent ``zero_sub⟩]
    return {
      view
      semantic
      semanticDomainType := ← exactExpressionSyntax prepared.presentation.domainType
      primitiveCertificate := ← exactExpressionSyntax primitive
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      removedConstraintNames := {}
      normalizationLemmas
      checkpoint? := some { semantic, view }
      constraintSplices := prepared.replacedIndices.map fun index =>
        { index, count := (prepared.rowOrigins.filter (· == index)).size }
      terminalForm? := some (← exactExpressionSyntax form)
      status := .terminal
    }

/-- Plan the complete exact conversion and request all generated local names. -/
def prepareTerminalConic (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft := withRef step do
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    match ← Morew.Elab.Conic.Terminal.plan presentation with
    | .error error => throwError "terminal conic validation is uncertified: {error.reason}"
    | .ok result => pure (result, sectionFVars)
  let mut nameRequests := #[]
  for i in [:prepared.auxiliaries.size] do
    let stem ← terminalStem state prepared.auxiliaries[i]!.1
    nameRequests := nameRequests.push {
      id := i, kind := .generatedBinderFamily
      requested := Name.mkSimple (stem ++ "_aux"), ref := step }
  let mut counts := Array.replicate state.view.constraints.size 0
  for i in [:prepared.rowOrigins.size] do
    let origin := prepared.rowOrigins[i]!
    if prepared.replacedIndices.contains origin then
      let count := counts[origin]! + 1
      counts := counts.set! origin count
      let stem ← terminalStem state origin
      nameRequests := nameRequests.push {
        id := prepared.auxiliaries.size + i, kind := .generatedRowFamily
        requested := Name.mkSimple s!"{stem}_conic_{count}", ref := step }
  return { nameRequests, materialize := materializeTerminalConic state prepared preparedVars }

end Morew.Reformulation.Internal
