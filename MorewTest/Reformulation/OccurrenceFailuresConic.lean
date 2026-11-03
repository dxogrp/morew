/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-! Terminal conic steps reject later occurrence bounds without retaining outputs. -/

namespace MorewTest.Reformulation.OccurrenceFailures

open Morew
noncomputable section

def terminalSource := problem (x : ℝ) minimize x

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs (substring := true) in
reformulation afterTerminal : terminalSource certificate afterTerminalAlias := by
  conic
  epigraph t at (x)

assert_not_exists afterTerminal afterTerminal.equivalence afterTerminalAlias

run_cmd do
  if (Syntax.getProblemView? (← Lean.getEnv)
      `MorewTest.Reformulation.OccurrenceFailures.afterTerminal).isSome then
    Lean.throwError "failed occurrence lift registered presentation metadata"

end
end MorewTest.Reformulation.OccurrenceFailures
