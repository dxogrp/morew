/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Reformulation.Rows

/-!
# Certified restrictions

Append a constraint using an explicit improvement from the current problem to
its restriction. This may discard feasible points; the proof supplies
retained representatives with objectives no worse in the optimization order.
-/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def restrictStyle : Rows.Append.Style := {
  description := "restriction"
  certificateKind := `restrictedConstraint
  family := "restricted"
}

private def materializeRestrict (state : ReformState) (label : TSyntax `ident)
    (proposition provided : TSyntax `term)
    (allocation : Morew.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let some name := allocation.findName? 0
    | throwErrorAt label "internal error: missing restriction label allocation"
  runTermElabM fun sectionFVars => withoutErrToSorry do
    let typed := state.typed.replaceFVars state.sectionFVars sectionFVars
    let (predicate, propositionSyntax) ←
      Rows.Append.elaboratePredicate restrictStyle state typed proposition
    let natural ← mkAppM ``Morew.Problem.addConstraint #[typed.semantic, predicate]
    let expected ← mkAppM ``Morew.GlobalImprovement #[typed.semantic, natural]
    -- The repair concerns the complete current problem. Neither temporary
    -- model bindings nor the proposed restriction enter its source evidence.
    let improvement ← withRef provided do
      let proof ← elabTermEnsuringType provided expected
      synthesizeSyntheticMVarsNoPostponing
      if (← getThe Core.State).messages.hasErrors then throwAbortTerm
      let proof ← instantiateMVars proof
      if proof.hasMVar || proof.hasSorry then
        throwError "restriction certificate contains unresolved metavariables or placeholders"
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        checkWithKernel proof
      pure proof
    let addition ← mkAppM ``Morew.restrictionEquivalence
      #[typed.semantic, predicate, improvement]
    Rows.Append.finish restrictStyle state typed name proposition
      predicate propositionSyntax addition

/-- Preflight the explicit label before elaborating a restriction or its certificate. -/
def prepareRestrict (state : ReformState) (label : TSyntax `ident)
    (proposition provided : TSyntax `term) : CommandElabM SurfaceStepDraft :=
  pure {
    nameRequests := #[{
      id := 0, kind := .explicitConstraintLabel
      requested := label.getId.eraseMacroScopes, ref := label.raw }]
    materialize := materializeRestrict state label proposition provided
  }

@[morew_reformulation_step Morew.restrictStep]
private def elabRestrict : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| restrict $label:ident : $proposition:term using $provided:term) =>
      prepareRestrict state label proposition provided
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
