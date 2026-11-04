/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Basic.Rename
import Morew.Elab.Reformulation.Step
import MorewTest.Environment

/-!
# Renaming preserves runner state and certificate relations

A synthetic equality relation makes a hard-coded global-equivalence primitive
fail. Scoped selectors also exercise visible-name no-ops independently of the
reformulation command's fixed public runner.
-/

namespace MorewTest.Reformulation.RenameIsolation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew Morew.Elab.Reformulation

def source :=
  problem (n : Nat)
    minimize n
    subject to
      first : n ≤ 3
      middle : n ≤ 5
      last : True

def LabelRelation (left right : Problem Nat Nat) : Prop := left = right

theorem LabelRelation.reflexivity (p : Problem Nat Nat) :
    LabelRelation p p := rfl

theorem LabelRelation.transitivity {left middle right : Problem Nat Nat}
    (first : LabelRelation left middle) (second : LabelRelation middle right) :
    LabelRelation left right := first.trans second

private def labelRunner : CertificateRunner := {
  relation := ``LabelRelation
  refl := ``LabelRelation.reflexivity
  trans := ``LabelRelation.transitivity
}

run_cmd do
  let sparseRemoved : Std.HashSet Nat :=
    (({} : Std.HashSet Nat).insert 0 |>.insert 2 |>.insert 4)
  match validateCheckpointRows 5 2 #[1, 3] sparseRemoved with
  | .ok () => pure ()
  | .error error => throwError "valid sparse checkpoint inventory was rejected: {error}"
  match validateCheckpointRows 0 0 #[] {} with
  | .ok () => pure ()
  | .error error => throwError "empty checkpoint inventory was rejected: {error}"
  let cases : Array (String × Nat × Array Nat × Std.HashSet Nat) := #[
    ("row count", 3, #[0, 1], ({} : Std.HashSet Nat).insert 2),
    ("duplicate", 2, #[0, 0], ({} : Std.HashSet Nat).insert 1 |>.insert 2),
    ("reordered", 2, #[1, 0], ({} : Std.HashSet Nat).insert 2),
    ("live out of bounds", 2, #[0, 3], ({} : Std.HashSet Nat).insert 1),
    ("removed out of bounds", 2, #[0, 1], ({} : Std.HashSet Nat).insert 3),
    ("missing", 1, #[0], ({} : Std.HashSet Nat).insert 1),
    ("overlap", 2, #[0, 2], ({} : Std.HashSet Nat).insert 1 |>.insert 2)
  ]
  for (description, rowCount, live, removed) in cases do
    match validateCheckpointRows 3 rowCount live removed with
    | .error _ => pure ()
    | .ok () => throwError "invalid {description} checkpoint inventory was accepted"

private def initialState : CommandElabM ReformState := do
  let (typed, sectionFVars, view, semantic) ← runTermElabM fun sectionFVars => do
    let some view := Morew.Syntax.getProblemView? (← getEnv) ``source
      | throwError "missing source presentation"
    let semantic := Lean.mkConst ``source
    let canonical ← canonicalTargetExpressionFromExpressions ``source semantic semantic
      view {} semantic false
    let presentation ← typedPresentationFromExpression canonical view
    let normalization ← checkedPointwiseNormalization ``source semantic canonical #[]
    let accumulatedCertificate ← labelRunner.reflexivity semantic
    let typed : Morew.Elab.Reformulation.RunnerState := {
      semantic
      canonical
      semanticDomainType := Lean.mkConst ``Nat
      semanticValueType := Lean.mkConst ``Nat
      presentation
      accumulatedCertificate
      normalization
    }
    pure (typed, sectionFVars, view, ← exactExpressionSyntax semantic)
  return {
    typed
    sectionFVars
    view
    semantic
    semanticDomainType := ← liftMacroM `(Nat)
    semanticValueType := ← liftMacroM `(Nat)
    certificateSyntax := ← liftMacroM <| certificateReflTerm labelRunner semantic
    source := semantic
    sourceName := ``source
    checkpoint := { semantic, semanticAnchor := semantic, view }
    liveCheckpointRows := Array.range view.constraints.size
    runner := labelRunner
  }

run_cmd do
  let state ← initialState
  let scopedSource : TSyntax `ident :=
    ⟨mkIdent (Lean.addMacroScope `RenameIsolation `middle 17)⟩
  let scopedSame : TSyntax `ident :=
    ⟨mkIdent (Lean.addMacroScope `RenameIsolation `middle 18)⟩
  let noOp ← prepareRenameConstraint state scopedSource scopedSame
  unless noOp.nameRequests.isEmpty do
    throwError "same-visible-name renaming requested an occupied name"
  let noOpSurface ← noOp.materialize #[]
  unless noOpSurface.view.constraints[1]!.name == state.view.constraints[1]!.name do
    throwError "same-visible-name renaming changed the original scoped name"
  let (noOpResult, noOpMaterialization) ← runTypedStepPlan state noOp
  let noOpState ← commitSurfaceStep state noOpResult noOpMaterialization
  unless noOpState.typed.status == .continue do
    throwError "same-visible-name renaming became terminal"

  let scopedDestination : TSyntax `ident :=
    ⟨mkIdent (Lean.addMacroScope `RenameIsolation `labels.renamed 19)⟩
  let draft ← prepareRenameConstraint state scopedSource scopedDestination
  let some request := draft.nameRequests[0]?
    | throwError "renaming did not request its destination"
  unless draft.nameRequests.size == 1 &&
      request.requested == `labels.renamed do
    throwError "renaming did not request the exact visible destination"
  let before ← getEnv
  let (result, materialization) ← runTypedStepPlan state draft
  unless result.presentationDelta.constraintAdditions.isEmpty do
    throwError "renaming was represented as a tail addition"
  let next ← commitSurfaceStep state result materialization
  unless MorewTest.sameLocalDeclarationNames before (← getEnv) do
    throwError "renaming emitted helper declarations"
  unless next.semantic.raw == state.semantic.raw &&
      next.semanticDomainType.raw == state.semanticDomainType.raw &&
      next.semanticValueType.raw == state.semanticValueType.raw do
    throwError "renaming changed the natural semantic problem or its types"
  unless next.checkpoint.semantic.raw == state.checkpoint.semantic.raw &&
      next.checkpoint.semanticAnchor.raw == state.checkpoint.semanticAnchor.raw &&
      next.liveCheckpointRows == state.liveCheckpointRows &&
      next.removedCheckpointRows.toArray == state.removedCheckpointRows.toArray do
    throwError "renaming changed checkpoint provenance"
  unless next.view.objective == state.view.objective &&
      next.view.constraints.map (·.proposition) == state.view.constraints.map (·.proposition) do
    throwError "renaming changed an objective or constraint expression"
  unless next.view.constraints.map (·.name.eraseMacroScopes) ==
      #[`first, `labels.renamed, `last] do
    throwError "renaming moved or changed an unselected row"
  let inventory := next.typed.presentation.nameInventory
  unless !inventory.contains .constraintLabel `middle &&
      inventory.contains .constraintLabel `labels.renamed do
    throwError "renaming retained an alias or failed to occupy its destination"
  unless next.typed.status == .continue && next.typed.companions.isEmpty do
    throwError "renaming changed terminal state or requested companions"
  runTermElabM fun sectionFVars => do
    let original := state.typed.replaceFVars state.sectionFVars sectionFVars
    let committed := next.typed.replaceFVars next.sectionFVars sectionFVars
    unless committed.semantic == original.semantic &&
        (← isDefEq committed.canonical original.canonical) do
      throwError "renaming changed the typed semantic or canonical problem"
    for index in [:original.presentation.constraints.size] do
      unless ← isDefEq original.presentation.constraints[index]!.predicate
          committed.presentation.constraints[index]!.predicate do
        throwError "renaming changed the predicate at index {index}"
    let expected ← labelRunner.relationType original.semantic original.semantic
    unless ← isDefEq (← inferType committed.accumulatedCertificate) expected do
      throwError "renaming changed the configured certificate relation"
    checkWithKernel committed.accumulatedCertificate

end MorewTest.Reformulation.RenameIsolation
