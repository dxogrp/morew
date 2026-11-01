/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Append

/-!
# Certified restrictions

Append a constraint using an explicit improvement from the current problem to
its restriction. This may discard feasible points; the certificate supplies
retained representatives with objectives no worse in the optimization order.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def restrictStyle : Append.Style := {
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
      Append.elaboratePredicate restrictStyle state typed proposition
    let natural ← mkAppM ``Morew.Problem.addConstraint #[typed.semantic, predicate]
    let expected ← mkAppM ``Morew.GlobalImprovement #[typed.semantic, natural]
    -- The repair concerns the complete current problem. Neither temporary
    -- model bindings nor the proposed restriction enter its source evidence.
    let improvement ← withRef provided do
      let certificate ← elabTermEnsuringType provided expected
      synthesizeSyntheticMVarsNoPostponing
      if (← getThe Core.State).messages.hasErrors then throwAbortTerm
      let certificate ← instantiateMVars certificate
      if certificate.hasMVar || certificate.hasSorry then
        throwError "restriction certificate contains unresolved metavariables or placeholders"
      withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
        checkWithKernel certificate
      pure certificate
    let addition ← mkAppM ``Morew.restrictionEquivalence
      #[typed.semantic, predicate, improvement]
    Append.finish restrictStyle state typed name proposition
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

end Morew.Reformulation.Internal
