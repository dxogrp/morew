/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.State
import Morew.Elab.Reformulation.Syntax

/-!
# Internal reformulation dispatch

Entry points install exactly one handler for each supported syntax kind. This
registry is command implementation machinery, not a public extension API.
-/

namespace Morew.Elab.Reformulation

open Lean Lean.Elab Lean.Elab.Command

/-- Prepare one primitive command step without committing runner state. -/
abbrev StepHandler := ReformState → Syntax → CommandElabM SurfaceStepDraft

private unsafe def mkStepAttributeUnsafe (ref : Name) : IO (KeyedDeclsAttribute StepHandler) :=
  mkElabAttribute StepHandler `builtin_morew_reformulation_step `morew_reformulation_step
    `Morew ``StepHandler "internal reformulation step" ref

@[implemented_by mkStepAttributeUnsafe]
private opaque mkStepAttribute (ref : Name) : IO (KeyedDeclsAttribute StepHandler)

/-- Internal syntax-kind dispatch table populated by the selected entry point. -/
initialize stepAttribute : KeyedDeclsAttribute StepHandler ← mkStepAttribute decl_name%

/-- Resolve exactly one installed handler and prepare its uncommitted step. -/
def prepareStep (state : ReformState) (step : Syntax) : CommandElabM SurfaceStepDraft := do
  match stepAttribute.getEntries (← getEnv) step.getKind with
  | [entry] => withRef step <| entry.value state step
  | [] =>
    let required := if step.isOfKind ``Morew.conicStep || step.isOfKind ``Morew.conicAtStep then
        "Morew.Reformulation.Conic"
      else if step.isOfKind ``Morew.nlpStep || step.isOfKind ``Morew.nlpAtStep then
        "Morew.Reformulation.NLP"
      else "Morew.Reformulation.Basic"
    throwErrorAt step "reformulation step is unavailable; import {required}"
  | _ => throwErrorAt step
      "multiple internal handlers registered for reformulation step `{step.getKind}`"

end Morew.Elab.Reformulation
