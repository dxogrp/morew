/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Conic.Terminal
import Morew.Elab.Reformulation.Rows
import Morew.Elab.Expr
import Morew.Elab.Rewrite.Reduction

/-! Convert nonlinear rows exactly and normalize affine comparisons to cone membership.
Preserve named affine groups and local definitions. Allocate generated names together and
emit a structural form beside the target. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

-- Store section-dependent expressions with the certificate.
private def validateTerminalConic (form expected : Expr)
    (sense : Morew.ObjectiveSense) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  unless type.isAppOfArity ``Morew.Conic.Form 5 do
    throwError "terminal evidence is not a Conic.Form"
  let represented := type.getAppArgs.back!
  unless ← isDefEq represented expected do
    throwError "terminal conic form does not represent the final canonical problem"
  let data ← mkProjection form `data
  let actualSense ← mkProjection data `sense
  let expectedSense := match sense with
    | .minimize => mkConst ``Morew.ObjectiveSense.minimize
    | .maximize => mkConst ``Morew.ObjectiveSense.maximize
  unless ← isDefEq actualSense expectedSense do
    throwError "terminal conic form has the wrong objective sense"
  pure represented

private def retargetTerminalConic (form target equality : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  let arguments := type.getAppArgs.set! (type.getAppNumArgs - 1) target
  let represents ← mkAppM ``Eq.trans #[← mkProjection form `represents, equality]
  let data ← mkProjection form `data
  pure <| mkAppN (mkConst ``Morew.Conic.Form.mk type.getAppFn.constLevels!)
    (arguments ++ #[data, represents])

private def terminalConicProperty (form : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  pure <| mkAppN (mkConst ``Morew.Conic.Form.isConic type.getAppFn.constLevels!)
    (type.getAppArgs ++ #[form])

private def terminalConicAdapter : TerminalAdapter := {
  description := "conic"
  formSuffix := `conicForm
  propertySuffix := `isConic
  validate := validateTerminalConic
  retarget := retargetTerminalConic
  property := terminalConicProperty
}

private def terminalStem (state : ReformState) (origin : Nat) : CommandElabM String := do
  let name := state.view.constraints[origin]!.name.eraseMacroScopes
  let .str _ stem := name
    | throwError "cannot derive a generated-name family from constraint `{name}`"
  return stem

private def positiveSemidefiniteMembership {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) (symmetric : matrix.IsSymm) : Prop :=
  Morew.Conic.SymmetricMatrix.ofMatrix matrix symmetric ∈
    (Morew.Conic.Cone.positiveSemidefinite n).carrier

private theorem retainedMatrixIsSymm {n : ℕ}
    {retained checked : Matrix (Fin n) (Fin n) ℝ}
    (equality : retained = checked) (symmetry : checked.IsSymm) : retained.IsSymm :=
  equality.symm ▸ symmetry

-- Recover semantic symmetry evidence and transport it along checked matrix equalities.
private def normalizeRetainedPositiveSemidefinite (normalizationProof : Term)
    (original target : Expr) : TermElabM Morew.Elab.Conic.BodyNormalization := do
  unless original.isAppOf ``Matrix.PosSemidef &&
      target.isAppOfArity ``Membership.mem 5 do
    throwError "retained PSD predicate does not match the checked membership target"
  let value := target.getAppArgs[4]!
  unless value.isAppOfArity ``Morew.Conic.SymmetricMatrix.ofMatrix 3 do
    throwError "checked PSD membership is missing its symmetric matrix conversion"
  let matrix := original.getAppArgs.back!
  let checkedMatrix := value.getAppArgs[1]!
  let mut symmetry := value.getAppArgs[2]!
  unless ← isDefEq matrix checkedMatrix do
    let equalityType ← zetaReduce (← mkEq matrix checkedMatrix)
    let equality ← elabTerm normalizationProof (some equalityType)
    synthesizeSyntheticMVarsNoPostponing
    let equality ← instantiateMVars equality
    checkWithKernel equality
    symmetry ← mkAppM ``retainedMatrixIsSymm #[equality, symmetry]
  let converted ← mkAppM ``Morew.Conic.SymmetricMatrix.ofMatrix #[matrix, symmetry]
  let some body ← unfoldDefinition? (← mkAppM ``positiveSemidefiniteMembership
    #[matrix, symmetry])
    | throwError "could not reconstruct retained PSD membership"
  let iff ← mkAppM ``Iff.symm
    #[← mkAppM ``Morew.Conic.Cone.mem_positiveSemidefinite #[converted]]
  unless ← isDefEq (← inferType iff) (mkApp2 (mkConst ``Iff) original body) do
    throwError "retained PSD membership does not match its original predicate"
  checkWithKernel iff
  return { body, iff, changed := true }

-- Follow accepted structural reductions while preserving operands and model-local bindings.
private partial def normalizeRetainedBody (normalizationProof : Term)
    (original target : Expr) : TermElabM Morew.Elab.Conic.BodyNormalization := do
  let body ← Morew.Elab.Expr.reduceStructure original (preserveLets := true)
  let target ← Morew.Elab.Expr.reduceStructure target
  if let .letE name type value rest _ := body then
    -- Make source lets reducible when generated symmetry proofs depend on their values.
    return ← withLetDecl name type value fun binding => do
      let result ← normalizeRetainedBody normalizationProof (rest.instantiate1 binding) target
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
    let left ← normalizeRetainedBody normalizationProof args[0]! targets[0]!
    let right ← normalizeRetainedBody normalizationProof args[1]! targets[1]!
    return {
      body := mkApp2 (mkConst ``And) left.body right.body
      iff := ← mkAppM ``and_congr #[left.iff, right.iff]
      changed := left.changed || right.changed
    }
  if ← isDefEq body (mkConst ``True) then
    return { body := original, iff := mkApp (mkConst ``Iff.rfl) original, changed := false }
  if body.isAppOf ``Matrix.PosSemidef then
    return ← normalizeRetainedPositiveSemidefinite normalizationProof body target
  let normalized : Except Exception Morew.Elab.Conic.BodyNormalization ← try
      pure (.ok (← Morew.Elab.Conic.normalizeBody original))
    catch error => pure (.error error)
  if let .ok result := normalized then
    if result.changed then return result
    -- Preserve native memberships while checking substituted operands by normalization.
    if body.isAppOfArity ``Membership.mem 5 && target.isAppOfArity ``Membership.mem 5 then
      if (← isDefEq body.getAppArgs[2]! target.getAppArgs[2]!) &&
          (← isDefEq body.getAppArgs[3]! target.getAppArgs[3]!) then return result
  -- Expose accepted comparisons through structural reduction and registered field accessors.
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
  let result ← normalizeRetainedBody normalizationProof exposed target
  unless result.changed do
    return { body := original, iff := mkApp (mkConst ``Iff.rfl) original, changed := false }
  let expected := mkApp2 (mkConst ``Iff) original result.body
  unless ← isDefEq (← inferType result.iff) expected do
    throwError "retained membership normalization does not match the source proposition"
  return result

-- Normalize retained entries in their original binding scope; use planner expressions
-- for generated entries. Check the complete view against the canonical problem.
private def normalizeRetainedView (sourceName : Name) (normalizationLemmas : Array Term)
    (prepared : Morew.Elab.Conic.Terminal.Result)
    (template rendered : Morew.Syntax.ProblemView) : TermElabM Morew.Syntax.ProblemView := do
  let simpLemmas ← liftMacroM <| normalizationSimpLemmas sourceName normalizationLemmas
  let normalizationProof ← liftMacroM `(by simp only [$[$simpLemmas],*] <;> rfl)
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
        let normalized ← normalizeRetainedBody normalizationProof body
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
    let exact ← mkAppM ``Morew.GlobalEquiv.trans
      #[typed.normalization.equiv, prepared.equiv]
    let primitive ← state.runner.liftEquiv exact
    let candidates := (typed.presentation.constraints ++ prepared.presentation.constraints).toList
      |>.zipIdx |>.map fun (row, index) => (Name.mkSimple s!"terminal_row_{index}", row.predicate)
    let primitive ← Rows.storeCertificate `_terminalConicCertificate primitive
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
    -- Prove agreement with reduced zero/negation definitions while retaining their display names.
    let normalizationLemmas := state.normalizationLemmas ++
      #[⟨mkCIdent ``sub_zero⟩, ⟨mkCIdent ``zero_sub⟩,
        ⟨mkCIdent ``sub_neg_eq_add⟩, ⟨mkCIdent ``zero_add⟩, ⟨mkCIdent ``neg_neg⟩]
    let view ← normalizeRetainedView state.sourceName normalizationLemmas prepared template rendered
    let semantic ← exactExpressionSyntax targetProblem
    let formName ← mkAuxDeclName (kind := `_terminalConicForm)
    let form ← mkAuxDefinitionFor formName prepared.form (zetaDelta := true) (compile := false)
    modifyEnv (addNoncomputable · formName)
    return {
      view
      semantic
      semanticDomainType := ← exactExpressionSyntax prepared.presentation.domainType
      primitiveCertificate := ← exactExpressionSyntax primitive
      simplifyExpLogTerms := state.simplifyExpLogTerms
      hasSubstitution := state.hasSubstitution
      liveCheckpointRows := Array.range view.constraints.size
      removedCheckpointRows := {}
      normalizationLemmas
      checkpoint? := some { semantic, semanticAnchor := semantic, view }
      constraintSplices := prepared.replacedIndices.map fun index =>
        { index, count := (prepared.rowOrigins.filter (· == index)).size }
      terminalForm? := some (terminalConicAdapter, ← exactExpressionSyntax form)
      status := .terminal
    }

-- Reduce explicit class constructors only after direct conic certification.
private def normalizeDirectPresentation (presentation : PresentationState) : MetaM PresentationState := do
  let result ← Morew.Elab.Conic.Plan.withPresentationFiniteInstances
      (fun result oldVars newVars => result.replaceFVars oldVars newVars) presentation do
    let reduce := fun expression => dsimpPreservingProofLets expression (preserveOperations := false)
    let objective ← Morew.Elab.Rewrite.Reduction.normalize presentation.objective reduce fun candidate => do
      return (← Morew.Elab.Conic.reifyObjective { presentation with objective := candidate }).isOk
    let constraints ← presentation.constraints.mapM fun row => do
      let predicate ← Morew.Elab.Rewrite.Reduction.normalizePredicate row.predicate reduce fun candidate => do
        let (leaves, _) ← Morew.Elab.Rewrite.decomposePredicate candidate
        for leaf in leaves do
          if let .error _ ← Morew.Elab.Conic.normalizeRow leaf then return false
        return true
      return { row with predicate }
    return .ok { presentation with objective, constraints }
  return result.toOption.getD presentation

/-- Plan the complete exact conversion and request all generated local names. -/
def prepareTerminalConic (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft := withRef step do
  let (prepared, preparedVars) ← runTermElabM fun sectionFVars => do
    let presentation := state.typed.presentation.replaceFVars state.sectionFVars sectionFVars
    let presentation ← normalizeDirectPresentation presentation
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

@[morew_reformulation_step Morew.conicStep]
private def elabConic : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| conic) => prepareTerminalConic state step
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
