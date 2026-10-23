import Lean.Meta.Basic

/-!
# State isolation for certified affine recognition

Recognition must not assign caller metavariables. Successful proof terms may,
however, depend on auxiliary declarations produced by an evidence callback.
-/

namespace Morew.Elab.Affine

open Lean Lean.Meta

/-- Run recognition without changing caller metavariables, preserving auxiliary
declarations only when it succeeds. Failed recognition also rolls back the
environment. Name generators remain advanced, as in Lean's standard state
restoration, so retained auxiliary declarations cannot collide with later ones.

Already assigned metavariables in local declarations are instantiated in a
temporary context, allowing kernel checking without modifying the caller's
declarations.

Restoring the environment through `setEnv` clears both core and meta caches:
their entries may refer to discarded metavariables or declarations. -/
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

end Morew.Elab.Affine
