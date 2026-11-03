/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.DiagnosticsSupport
import MorewTest.Environment

/-! # Removal proof completeness, isolated attempts, and the configured runner -/

namespace MorewTest.Reformulation.RemoveIsolation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew Morew.Elab.Reformulation
noncomputable section

elab "remove_missing%" : term <= expected => do
  mkFreshExprMVar expected

elab "remove_synthetic_sorry%" : term <= expected => do
  mkSorry expected true

elab "remove_user_sorry%" : term <= expected => do
  mkSorry expected false

elab "remove_completed%" : term <= expected => do
  let proof ← elabTermEnsuringType (← `(by intro _ _; trivial)) expected
  synthesizeSyntheticMVarsNoPostponing
  let hole ← mkFreshExprMVar expected
  hole.mvarId!.assign (← instantiateMVars proof)
  pure hole

elab "assert_remove_isolated% " target:ident " in " nested:command : command => do
  let before ← getEnv
  let target := (← getCurrNamespace) ++ target.getId
  try elabCommand nested catch error => Lean.Elab.logException error
  let after ← getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    throwError "rejected incomplete removal changed declarations"
  for name in #[target, target ++ `equivalence] do
    if after.contains name || (Morew.Syntax.getProblemView? after name).isSome then
      throwError "rejected incomplete removal retained an output or its metadata"

def source :=
  problem (n : Nat)
    minimize n
    subject to
      first : n ≤ 3
      middle : n ≤ 3
      last : True

#guard_error_fragments ["constraint removal proof", "placeholders"] in
assert_remove_isolated% userProof in
reformulation userProof : source := by
  remove at middle using remove_user_sorry%

#guard_error_fragments ["constraint removal proof", "placeholders"] in
assert_remove_isolated% syntheticProof in
reformulation syntheticProof : source := by
  remove at middle using remove_synthetic_sorry%

#guard_error_fragments ["constraint removal proof", "unresolved metavariables"] in
assert_remove_isolated% missingProof in
reformulation missingProof : source := by
  remove at middle using remove_missing%

#guard_error_fragments ["constraint removal proof", "placeholders"] in
assert_remove_isolated% latePlaceholder in
reformulation latePlaceholder : source := by
  remove at last using remove_completed%
  remove at middle using remove_synthetic_sorry%

reformulation latePlaceholder : source := by
  remove at last using remove_completed%

example : GlobalEquivalence source latePlaceholder := latePlaceholder.equivalence
example (n : Nat) : latePlaceholder.feasible n ↔ n ≤ 3 ∧ n ≤ 3 := Iff.rfl

-- A distinct relation requires the handler to lift its primitive equivalence
-- through the runner, instead of hard-coding the public relation throughout.
structure TestRelation (left right : Problem Nat Nat) where
  equivalence : GlobalEquivalence left right

def TestRelation.reflexivity (p : Problem Nat Nat) : TestRelation p p :=
  ⟨GlobalEquivalence.refl p⟩

def TestRelation.transitivity {left middle right : Problem Nat Nat}
    (first : TestRelation left middle) (second : TestRelation middle right) :
    TestRelation left right := ⟨first.equivalence.trans second.equivalence⟩

def TestRelation.ofEquivalence {left right : Problem Nat Nat}
    (witness : GlobalEquivalence left right) : TestRelation left right := ⟨witness⟩

private def testRunner : CertificateRunner := {
  relation := ``TestRelation
  refl := ``TestRelation.reflexivity
  trans := ``TestRelation.transitivity
  liftEquivalence? := some ``TestRelation.ofEquivalence
}

private def initialState : CommandElabM ReformState := do
  let (typed, sectionFVars, view, semantic) ← runTermElabM fun sectionFVars => do
    let some view := Syntax.getProblemView? (← getEnv) ``source
      | throwError "missing source presentation"
    let semantic := Lean.mkConst ``source
    let canonical ← canonicalTargetExpressionFromExpressions ``source semantic semantic
      view {} semantic false
    let presentation ← typedPresentationFromExpression canonical view
    let normalization ← checkedPointwiseNormalization ``source semantic canonical #[]
    let accumulatedCertificate ← testRunner.reflexivity semantic
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
    certificateSyntax := ← liftMacroM <| certificateReflTerm testRunner semantic
    source := semantic
    sourceName := ``source
    checkpoint := { semantic, semanticAnchor := semantic, view }
    liveCheckpointRows := Array.range view.constraints.size
    runner := testRunner
  }

run_cmd do
  let state ← initialState
  let scopedSelector : TSyntax `ident :=
    ⟨mkIdent (Lean.addMacroScope `RemoveIsolation `middle 17)⟩
  let draft ← prepareRemove state scopedSelector none
  unless draft.nameRequests.isEmpty do
    throwError "removal allocated a name or auxiliary"
  let (result, materialization) ← runTypedStepPlan state draft
  unless result.presentationDelta.constraintAdditions.isEmpty do
    throwError "removal became a tail addition"
  let next ← commitSurfaceStep state result materialization
  unless next.view.constraints.map (·.name.eraseMacroScopes) == #[`first, `last] do
    throwError "removal did not preserve neighboring labels and order"
  unless next.liveCheckpointRows == #[0, 1] && next.removedCheckpointRows.isEmpty do
    throwError "removal failed to establish a fresh checkpoint inventory"
  unless next.checkpoint.semantic.raw == next.checkpoint.semanticAnchor.raw do
    throwError "removal checkpoint failed to use the new semantic anchor"
  unless next.typed.status == .continue && next.typed.companions.isEmpty do
    throwError "removal changed terminal state or requested companions"
  unless !next.typed.presentation.nameInventory.contains .constraintLabel `middle do
    throwError "removal retained its old label in the name inventory"
  runTermElabM fun sectionFVars => do
    let original := state.typed.replaceFVars state.sectionFVars sectionFVars
    let committed := next.typed.replaceFVars next.sectionFVars sectionFVars
    let expected ← testRunner.relationType original.semantic committed.semantic
    unless ← isDefEq (← inferType committed.accumulatedCertificate) expected do
      throwError "removal ignored the configured certificate relation"
    checkWithKernel committed.accumulatedCertificate
    let presentation := original.presentation
    let predicateType ← mkArrow presentation.domainType (mkSort .zero)
    let unknown ← mkFreshExprMVar predicateType
    let entry := presentation.constraints[1]!
    let rows := presentation.constraints.set! 1 { entry with predicate := unknown }
    let incomplete := { presentation with constraints := rows }
    if (← Morew.Elab.Reformulation.Remove.prove? incomplete 1).isSome then
      throwError "incomplete selected predicate was solved by removal"
    if ← unknown.mvarId!.isAssigned then
      throwError "failed removal assigned a caller metavariable"
    let unrelated ← mkFreshExprMVar (Lean.mkConst ``Nat)
    let some proof ← Morew.Elab.Reformulation.Remove.prove? presentation 1
      | throwError "complete duplicate did not prove in the presence of a caller metavariable"
    checkWithKernel proof
    if ← unrelated.mvarId!.isAssigned then
      throwError "successful removal assigned an unrelated caller metavariable"
    -- Complete row predicates do not imply a complete presentation. The
    -- canonical-problem validation must not fill in the caller's other fields.
    for field in #["valueType", "binderType"] do
      let hole ← mkFreshExprMVar (mkSort (.succ .zero))
      let binder := presentation.binders[0]!
      let incomplete := if field == "valueType" then
          { presentation with valueType := hole }
        else { presentation with binders := #[{ binder with type := hole }] }
      let mut accepted := false
      try
        discard <| Morew.Elab.Reformulation.Remove.applyRemoval incomplete 1 proof
        accepted := true
      catch _ => pure ()
      if accepted then
        throwError "removal accepted an incomplete presentation {field}"
      if ← hole.mvarId!.isAssigned then
        throwError "removal assigned a caller metavariable in presentation {field}"

end
end MorewTest.Reformulation.RemoveIsolation
