/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Meta.Basic

/-! Scope temporary instances and isolate caller metavariables while retaining
successful certificates' auxiliary declarations. -/

namespace Morew.Elab.State

open Lean Lean.Meta

/-- Install instances in order, then substitute their values into the result.
Instantiate assigned metavariables before leaving the temporary local context. -/
def withInstances (name : Name) (instances : List Expr) (action : MetaM Expr) :
    MetaM Expr := do
  match instances with
  | [] => instantiateMVars (← action)
  | inst :: rest =>
      mapLetDeclZeta name (← inferType inst) inst fun _ =>
        withInstances name rest action

/-- Run recognition with fixed caller metavariables and retain declarations only on success.
Keep name generators advanced to avoid collisions. Instantiate assigned metavariables
in temporary local types for kernel checking. Restore failed environments through
`setEnv` to clear core and meta caches. -/
def withIsolatedMVars {ε α : Type} (action : MetaM (Except ε α)) :
    MetaM (Except ε α) := do
  let saved ← saveState
  let result ← try
    let context ← instantiateLCtxMVars (← getLCtx)
    withLCtx' context <| withNewMCtxDepth action
  catch error =>
    saved.restore
    setEnv saved.core.env
    throw error
  let environment ← match result with
    | .ok _ => getEnv
    | .error _ => pure saved.core.env
  saved.restore
  setEnv environment
  return result

end Morew.Elab.State
