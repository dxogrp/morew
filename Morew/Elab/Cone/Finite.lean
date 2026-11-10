/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Affine
import Morew.Elab.Rewrite.Plan
import Morew.Elab.Reformulation.Presentation
import Morew.Elab.State

/-! Retain finite-index evidence from source expressions during cone certification. -/

namespace Morew.Elab.Cone.Finite

open Lean Lean.Meta
open Morew.Elab.Rewrite.Plan

/-- Retry with finite evidence exposed by helpers; restore state before retrying original predicates. -/
def withHelperFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (sources : Array Expr)
    (action : MetaM (Except Expr.Error α)) :
    MetaM (Except Expr.Error α) := State.withIsolatedMVars do
  let failure (error : Exception) : MetaM (Except Expr.Error α) := do
    return Except.error ({
      expression := sources[0]?.getD (mkConst ``True)
      reason := ← addMessageContext error.toMessageData } : Expr.Error)
  try
    let replaceResult := fun result oldVars newVars =>
      result.map (fun value => replace value oldVars newVars)
    let direct ← State.withIsolatedMVars do
      try action catch error => failure error
    if let .ok result := direct then return .ok result
    let mut additional := #[]
    for source in sources do
      for inst in ← Affine.helperFiniteInstances source do
        unless additional.contains inst do
          additional := additional.push inst
    if additional.isEmpty then return direct
    withScopedFiniteInstances replaceResult additional.toList action
  catch error => failure error

/-- Collect finite-index evidence from the presentation and substitute temporary bindings
into the completed certificate. -/
def withPresentationFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (presentation : Reformulation.PresentationState)
    (action : MetaM (Except Expr.Error α)) :
    MetaM (Except Expr.Error α) := do
  let mut instances := #[]
  let sources := #[presentation.objective] ++ presentation.constraints.map (·.predicate)
  for source in sources do
    for inst in ← Expr.sourceFiniteInstances source do
      unless instances.contains inst do
        instances := instances.push inst
  withHelperFiniteInstances replace sources do
    withScopedFiniteInstances
      (fun result oldVars newVars => result.map (fun value => replace value oldVars newVars))
      instances.toList action

end Morew.Elab.Cone.Finite
