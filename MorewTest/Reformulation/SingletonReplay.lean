/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.Reformulation.PrintSupport
import MorewTest.Reformulation.ReplaySupport

/-! Scalar and vector singleton sets retain their types without importing conic or NLP commands. -/

namespace MorewTest.Reformulation.SingletonReplay

open Lean Lean.Elab.Command Morew
open MorewTest.Reformulation.PrintDetails (printed)

noncomputable section

def source :=
  problem (x : ℝ) (v : Fin 2 → ℝ)
    minimize x
    subject to
      scalar : x ∈ ({0} : Set ℝ)
      vector : v ∈ ({0} : Set (Fin 2 → ℝ))

reformulation target : source := by
  rename scalar to zeroScalar

run_cmd do
  for proofs in #[false, true] do
    let output ← printed ``target proofs
    for fragment in #["zeroScalar : x ∈ ({0} : Set ℝ)",
        "vector : v ∈ ({0} : Set (Fin 2 → ℝ))"] do
      unless output.contains fragment do
        throwError "singleton printing lost its collection type: {output}"

run_cmd do
  for (getter, name) in #[(Syntax.getProblemView?, `exactReplay),
      (Syntax.getProblemDisplayView?, `displayReplay)] do
    let some view := getter (← getEnv) ``target
      | throwError "singleton reformulation lost a stored reconstruction view"
    replayView view name
      "singleton replay contains incomplete evidence"

example : exactReplay = target := rfl
example : displayReplay = target := rfl

reformulation continued : displayReplay := by
  rename vector to zeroVector

example : continued = target := rfl
example : GlobalEquiv source continued :=
  target.equiv.trans continued.equiv
example (x : ℝ) (v : Fin 2 → ℝ) : continued.feasible (x, v) ↔
    x ∈ ({0} : Set ℝ) ∧ v ∈ ({0} : Set (Fin 2 → ℝ)) := Iff.rfl

end
end MorewTest.Reformulation.SingletonReplay
