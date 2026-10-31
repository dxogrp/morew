/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.Negation

/-! # Imported negated bounds preserve source spelling and exact certificates. -/

namespace MorewTest.ImportCompatibility.Negation

open Morew MorewTest.Reformulation.Negation

noncomputable section

reformulation continuedLog : logTarget := by conic

example : GlobalEquivalence logSource continuedLog :=
  logBound.equivalence.trans (logTarget.equivalence.trans continuedLog.equivalence)
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

example : GlobalEquivalence (normSource n) (continuedNorm n) :=
  (normBound.equivalence n).trans (continuedNorm.equivalence n)
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
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "negated-bound replay contains incomplete evidence"

example : sourceCopy = logSource := rfl
example : boundCopy = logBound := rfl
example : targetCopy = logTarget := rfl
example : customCopy center = MorewTest.Reformulation.Negation.Custom.target center := rfl

end Shadow

end
end MorewTest.ImportCompatibility.Negation
