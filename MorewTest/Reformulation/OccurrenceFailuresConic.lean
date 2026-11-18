/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

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

assert_not_exists afterTerminal afterTerminal.equiv afterTerminalAlias

run_cmd do
  let env ← Lean.getEnv
  let name := `MorewTest.Reformulation.OccurrenceFailures.afterTerminal
  for name in #[name, Lean.mkPrivateName env name] do
    if (Syntax.getProblemView? env name).isSome then
      Lean.throwError "failed occurrence lift registered presentation metadata"

end
end MorewTest.Reformulation.OccurrenceFailures
