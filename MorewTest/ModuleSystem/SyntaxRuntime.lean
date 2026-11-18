/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Syntax

/-! The syntax-only entry point preserves computable problem construction. -/

namespace MorewTest.ModuleSystem.SyntaxRuntime

def displayRow : Lean.CoreM Lean.Format :=
  (.nonneg .missing .missing false : Morew.Syntax.PowerChainRow).format
    (fun _ => pure "x")

def source : Morew.Problem Nat Nat :=
  problem (x : Nat) minimize x + 1 subject to upper : x ≤ 7

example (x : Nat) : source.objective x = x + 1 := rfl
example (x : Nat) : source.feasible x ↔ x ≤ 7 := Iff.rfl

/-- info: 4 -/
#guard_msgs in
#eval source.objective 3

end MorewTest.ModuleSystem.SyntaxRuntime
