/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.Negation
import MorewTest.Reformulation.ReplaySupport

/-! # Imported negated bounds preserve source spelling and exact certificates. -/

namespace MorewTest.ImportCompatibility.Negation

open Morew MorewTest.Reformulation.Negation

noncomputable section

reformulation continuedLog : logTarget := by conic

example : GlobalEquiv logSource continuedLog :=
  logBound.equiv.trans (logTarget.equiv.trans continuedLog.equiv)
example : IsConic continuedLog := continuedLog.isConic
example : continuedLog.conicForm.data.toProblem = continuedLog :=
  continuedLog.conicForm.represents
example : continuedLog.conicForm.data.rowCount = 3 := rfl

/--
info: problem (x t : ℝ)
  let loss := -Real.log x
  minimize t
  subject to
    domain : x - 1 ∈ ℝ₊
    cap : 3 - x ∈ ℝ₊
    lossBound_conic_1 : (-t, 1, x) ∈ EXP
-/
#guard_msgs in
#printp continuedLog

variable (n : Nat)

reformulation continuedNorm : (normBound n) := by conic

example : GlobalEquiv (normSource n) (continuedNorm n) :=
  (normBound.equiv n).trans (continuedNorm.equiv n)
example : IsConic (continuedNorm n) := continuedNorm.isConic n
example : (continuedNorm.conicForm n).data.sense = .maximize := rfl

namespace Shadow

def Real.log (x : ℝ) : ℝ := x + 100
def Custom.reward (center x : ℝ) : ℝ := x + center + 100

variable (center : ℝ)

run_cmd do
  for (original, copied) in #[
      (``MorewTest.Reformulation.Negation.logSource, `sourceCopy),
      (``MorewTest.Reformulation.Negation.logBound, `boundCopy),
      (``MorewTest.Reformulation.Negation.logTarget, `targetCopy),
      (``MorewTest.Reformulation.Negation.Custom.target, `customCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported negated bound lost its presentation"
    MorewTest.Reformulation.replayView view copied
      "negated-bound replay contains incomplete evidence"

example : sourceCopy = logSource := rfl
example : boundCopy = logBound := rfl
example : targetCopy = logTarget := rfl
example : customCopy center = MorewTest.Reformulation.Negation.Custom.target center := rfl

end Shadow

end
end MorewTest.ImportCompatibility.Negation
