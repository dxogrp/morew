/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.View
import Morew.Elab.Cone.Terminal
import Morew.Elab.Expr
import Morew.Elab.Rewrite.Reduction

/-! Normalize retained and direct cone presentations while preserving model-local bindings
and the evidence checked by the shared terminal planner. -/

namespace Morew.Elab.Reformulation.Cone.Presentation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def psdMembership {n : ℕ}
    (matrix : Matrix (Fin n) (Fin n) ℝ) (symmetric : matrix.IsSymm) : Prop :=
  Morew.Conic.SymmetricMatrix.ofMatrix matrix symmetric ∈
    (Morew.Conic.Cone.psd n).carrier

private theorem retainedMatrixIsSymm {n : ℕ}
    {retained checked : Matrix (Fin n) (Fin n) ℝ}
    (equality : retained = checked) (symmetry : checked.IsSymm) : retained.IsSymm :=
  equality.symm ▸ symmetry

-- Recover semantic symmetry evidence and transport it along checked matrix equalities.
private def normalizeRetainedPSD (normalizationProof : Term)
    (original target : Expr) : TermElabM Morew.Elab.Cone.BodyNormalization := do
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
  let some body ← unfoldDefinition? (← mkAppM ``psdMembership
    #[matrix, symmetry])
    | throwError "could not reconstruct retained PSD membership"
  let iff ← mkAppM ``Iff.symm
    #[← mkAppM ``Morew.Conic.Cone.mem_psd #[converted]]
  unless ← isDefEq (← inferType iff) (mkApp2 (mkConst ``Iff) original body) do
    throwError "retained PSD membership does not match its original predicate"
  checkWithKernel iff
  return { body, iff, changed := true }

-- Follow accepted structural reductions while preserving operands and model-local bindings.
private partial def normalizeRetainedBody (normalizationProof : Term)
    (original target : Expr) : TermElabM Morew.Elab.Cone.BodyNormalization := do
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
    return ← normalizeRetainedPSD normalizationProof body target
  let normalized : Except Exception Morew.Elab.Cone.BodyNormalization ← try
      pure (.ok (← Morew.Elab.Cone.normalizeBody original))
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

/-- Normalize retained entries in their original binding scope and use planner expressions
for generated entries, checking the complete view against the canonical problem. -/
def normalizeRetainedView (sourceName : Name) (normalizationLemmas : Array Term)
    (prepared : Morew.Elab.Cone.Terminal.Result)
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

/-- Accept an objective reduction after checking it with the selected backend.
Accept each constraint reduction after certifying its cone rows. -/
def normalizeDirectPresentation (backend : Morew.Elab.Cone.Terminal.Backend)
    (presentation : PresentationState) : MetaM PresentationState := do
  let result ← Morew.Elab.Cone.Finite.withPresentationFiniteInstances
      (fun result oldVars newVars => result.replaceFVars oldVars newVars) presentation do
    let reduce := fun expression => dsimpPreservingProofLets expression (preserveOperations := false)
    let objective ← Morew.Elab.Rewrite.Reduction.normalize presentation.objective reduce fun candidate => do
      return (← backend.checkObjective { presentation with objective := candidate } {}).isOk
    let constraints ← presentation.constraints.mapM fun row => do
      let predicate ← Morew.Elab.Rewrite.Reduction.normalizePredicate row.predicate reduce fun candidate => do
        let (leaves, _) ← Morew.Elab.Rewrite.decomposePredicate candidate
        for leaf in leaves do
          if let .error _ ← Morew.Elab.Cone.normalizeRow leaf then return false
        return true
      return { row with predicate }
    return .ok { presentation with objective, constraints }
  return result.toOption.getD presentation

end Morew.Elab.Reformulation.Cone.Presentation
