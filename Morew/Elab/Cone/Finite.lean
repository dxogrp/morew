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

/-- Try the action directly, then retry with finite-index evidence exposed by helpers.
Restore failed attempts before retrying on the original expressions. -/
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

/-- Collect finite-index evidence from the objective and constraints.
Replace temporary instance bindings with their evidence in successful results. -/
def withPresentationFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (presentation : Reformulation.PresentationState)
    (action : MetaM (Except Expr.Error α)) :
    MetaM (Except Expr.Error α) := do
  let sources := #[presentation.objective] ++ presentation.constraints.map (·.predicate)
  let instances ← Expr.collectSourceFiniteInstances sources
  withHelperFiniteInstances replace sources do
    withScopedFiniteInstances
      (fun result oldVars newVars => result.map (fun value => replace value oldVars newVars))
      instances action

end Morew.Elab.Cone.Finite
