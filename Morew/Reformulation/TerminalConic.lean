/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Terminal
import Morew.Reformulation.Replace
import Morew.Elab.Expr

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

-- The semantic checkpoint can expose a custom relation, constant match, or
-- structure field while retained syntax still contains its original head.
-- After planning accepts the row, follow those reductions against its target.
-- Operand expressions and model-local bindings stay untouched; a leaf with no
-- comparisons to convert retains its original spelling.
private partial def normalizeRetainedBody (original target : Expr) :
    MetaM Morew.Elab.Conic.BodyNormalization := do
  let body ← Morew.Elab.Expr.reduceStructure original (preserveLets := true)
  let target ← Morew.Elab.Expr.reduceStructure target
  if let .letE name type value rest nondep := body then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← normalizeRetainedBody (rest.instantiate1 binding) target
      return {
        body := ← mkLetFVars #[binding] result.body
          (usedLetOnly := false) (generalizeNondepLet := false)
        iff := ← mkLetFVars #[binding] result.iff
          (usedLetOnly := false) (generalizeNondepLet := false)
        changed := result.changed
      }
  if body.isAppOfArity ``And 2 then
    unless target.isAppOfArity ``And 2 do
      throwError "retained conjunction does not match the checked conic target"
    let args := body.getAppArgs
    let targets := target.getAppArgs
    let left ← normalizeRetainedBody args[0]! targets[0]!
    let right ← normalizeRetainedBody args[1]! targets[1]!
    return {
      body := mkApp2 (mkConst ``And) left.body right.body
      iff := ← mkAppM ``and_congr #[left.iff, right.iff]
      changed := left.changed || right.changed
    }
  if ← isDefEq body (mkConst ``True) then
    return { body := original, iff := mkApp (mkConst ``Iff.rfl) original, changed := false }
  let normalized : Except Exception Morew.Elab.Conic.BodyNormalization ← try
      pure (.ok (← Morew.Elab.Conic.normalizeBody original))
    catch error => pure (.error error)
  if let .ok result := normalized then
    if result.changed then return result
    -- Native memberships retain their spelling even when earlier substitution
    -- lemmas are needed to identify their operands with the checked target.
    if body.isAppOfArity ``Membership.mem 5 && target.isAppOfArity ``Membership.mem 5 then
      if (← isDefEq body.getAppArgs[2]! target.getAppArgs[2]!) &&
          (← isDefEq body.getAppArgs[3]! target.getAppArgs[3]!) then return result
  -- Iota/projection reduction can expose an accepted comparison hidden behind
  -- a constant match or structure field. Only registered field accessors may
  -- delta-unfold here; other unchanged user function heads remain intact.
  let structural ← whnfCore body
  let exposed? ← if structural != body then pure (some structural)
    else do
      match ← reduceProjOf? body (fun _ => true) with
      | some projection => pure (some projection)
      | none =>
        match normalized with
        | .ok _ =>
          if body.isAppOfArity ``Membership.mem 5 then unfoldDefinition? body else pure none
        | .error _ => unfoldDefinition? body
  let some exposed := exposed? | match normalized with
    | .ok result => return result
    | .error error => throw error
  let exposed ← whnfCore exposed
  if exposed == body then
    throwError "retained relation did not reduce to the checked conic target"
  let result ← normalizeRetainedBody exposed target
  unless result.changed do
    return { body := original, iff := mkApp (mkConst ``Iff.rfl) original, changed := false }
  let expected := mkApp2 (mkConst ``Iff) original result.body
  unless ← isDefEq (← inferType result.iff) expected do
    throwError "retained membership normalization does not match the source proposition"
  return result

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
      let point ← packPoint decisions
      let constraints ← template.constraints.mapIdxM fun i row => do
        let origin := prepared.rowOrigins[i]!
        if prepared.replacedIndices.contains origin then
          return rendered.constraints[i]!
        unless prepared.changedBodies.contains origin do return row
        let body ← elabPresentationTerm ⟨row.proposition⟩ bindings (some (mkSort .zero))
        synthesizeSyntheticMVarsNoPostponing
        let body ← instantiateMVars body
        let normalized ← normalizeRetainedBody body
          (mkApp prepared.presentation.constraints[i]!.predicate point)
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
    let primitive ← Replace.storeCertificate `_terminalConicCertificate primitive
      (candidates ++ [(`terminal_source, typed.canonical), (`terminal_target, targetProblem)])
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
    -- Canonical predicates may have reduced a zero or negated model definition,
    -- while the retained view deliberately still refers to its binding. These
    -- equalities check their agreement without rewriting the displayed body.
    let normalizationLemmas := state.normalizationLemmas ++
      #[⟨mkCIdent ``sub_zero⟩, ⟨mkCIdent ``zero_sub⟩,
        ⟨mkCIdent ``sub_neg_eq_add⟩, ⟨mkCIdent ``zero_add⟩, ⟨mkCIdent ``neg_neg⟩]
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
      terminalForm? := some (.conic, ← exactExpressionSyntax form)
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
