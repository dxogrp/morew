/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.Diagnostics
import MorewTest.Environment

/-! Internal syntax dispatch rejects duplicate handlers without invoking either one. -/

namespace MorewTest.Reformulation.Dispatch

open Lean Lean.Elab.Command Morew Morew.Elab.Reformulation

noncomputable section

def source := problem (x : ℝ) minimize x

elab "assert_dispatch_atomic% " nested:command : command => do
  let before ← getEnv
  try elabCommand nested catch error => Lean.Elab.logException error
  unless MorewTest.sameLocalDeclarationNames before (← getEnv) do
    throwError "dispatch failure leaked a declaration"

section Duplicate

@[local morew_reformulation_step Morew.epigraphStep]
private def duplicate : StepHandler := fun _ _ =>
  throwError "a duplicate handler must never run"

#guard_error_fragments ["multiple internal handlers registered", "Morew.epigraphStep"] in
assert_dispatch_atomic%
reformulation target : source certificate aliasProof := by
  derive trivial_row : True using (fun _ _ => True.intro)
  epigraph t

assert_not_exists target target.equivalence aliasProof

run_cmd do
  let env ← getEnv
  let name := `MorewTest.Reformulation.Dispatch.target
  if (Syntax.getProblemView? env name).isSome ||
      (Syntax.getProblemDisplayView? env name).isSome ||
      (Syntax.getProblemPrintPresentation? env name).isSome then
    throwError "dispatch failure leaked presentation metadata"

end Duplicate

-- Local registration removal restores the original handler and failed output names.
reformulation target : source certificate aliasProof := by epigraph t
example : GlobalEquivalence source target := aliasProof

end
end MorewTest.Reformulation.Dispatch
