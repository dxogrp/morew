/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Replace

/-!
# Constraint-label renaming

Rename one current presentation row without changing its predicate or the
natural semantic problem. The shared runner owns exact-name preflight,
certificate composition, and atomic commitment.
-/

namespace Morew.Reformulation.Internal

open Lean Lean.Elab Lean.Elab.Command

private def materializeRenameConstraint (state : ReformState) (index : Nat)
    (destination : TSyntax `ident) (unchanged : Bool)
    (allocation : Morew.Elab.Reformulation.NameAllocation) :
    CommandElabM SurfaceStepResult := do
  let view ← if unchanged then
      pure state.view
    else do
      let some name := allocation.findName? 0
        | throwErrorAt destination "internal error: missing renamed constraint label allocation"
      let constraint := state.view.constraints[index]!
      pure { state.view with
        constraints := state.view.constraints.set! index { constraint with name } }
  let primitiveCertificate ← liftMacroM <|
    certificateReflTerm state.runner state.semantic
  return {
    view
    semantic := state.semantic
    semanticDomainType := state.semanticDomainType
    primitiveCertificate
    simplifyExpLogTerms := state.simplifyExpLogTerms
    hasSubstitution := state.hasSubstitution
    liveCheckpointRows := state.liveCheckpointRows
    removedCheckpointRows := state.removedCheckpointRows
    normalizationLemmas := state.normalizationLemmas
    constraintSplices := #[{ index, count := 1 }]
  }

/-- Resolve the current source label before preflighting the exact destination.
An existing row may keep its visible name, including across macro scopes. -/
def prepareRenameConstraint (state : ReformState)
    (source destination : TSyntax `ident) : CommandElabM SurfaceStepDraft := do
  let index ← Replace.findConstraint state source
  let unchanged := sameUserName state.view.constraints[index]!.name destination.getId
  return {
    nameRequests := if unchanged then #[] else #[{
      id := 0, kind := .explicitConstraintLabel
      requested := destination.getId.eraseMacroScopes, ref := destination.raw }]
    materialize := materializeRenameConstraint state index destination unchanged
  }

end Morew.Reformulation.Internal
