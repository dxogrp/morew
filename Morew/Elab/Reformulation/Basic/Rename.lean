/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Registry
import Morew.Elab.Reformulation.Rows

/-! Rename a constraint label while preserving its predicate and semantic problem. -/

namespace Morew.Elab.Reformulation

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

/-- Resolve the source label before checking the destination name.
A row may retain its visible name across macro scopes. -/
def prepareRenameConstraint (state : ReformState)
    (source destination : TSyntax `ident) : CommandElabM SurfaceStepDraft := do
  let index ← Rows.findConstraint state source
  let unchanged := sameVisibleName state.view.constraints[index]!.name destination.getId
  return {
    nameRequests := if unchanged then #[] else #[{
      id := 0, kind := .explicitConstraintLabel
      requested := destination.getId.eraseMacroScopes, ref := destination.raw }]
    materialize := materializeRenameConstraint state index destination unchanged
  }

@[morew_reformulation_step Morew.renameConstraintStep]
private def elabRename : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| rename $source:ident to $destination:ident) =>
      prepareRenameConstraint state source destination
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
