/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.NegatedOccurrence

/-! # Imported objective occurrences retain checked antitone contexts. -/

namespace MorewTest.ImportCompatibility.NegatedOccurrence

open Morew MorewTest.Reformulation.NegatedOccurrence
noncomputable section

reformulation continuedLog : logBound := by conic

example : GlobalEquiv logSource continuedLog :=
  logBound.equiv.trans continuedLog.equiv
example : IsConic continuedLog := continuedLog.isConic
example : continuedLog.conicForm.data.toProblem = continuedLog :=
  continuedLog.conicForm.represents

reformulation continuedAbs : absBound := by conic

example : GlobalEquiv absSource continuedAbs :=
  absBound.equiv.trans continuedAbs.equiv
example : IsConic continuedAbs := continuedAbs.isConic
example : continuedAbs.conicForm.data.sense = .maximize := rfl

-- Further objective occurrence selection uses the imported transformed
-- objective, including its surrounding unary negation.
reformulation continuedCompound : compoundBound := by
  hypograph total at (a + b)
  conic

example : GlobalEquiv compoundSource continuedCompound :=
  compoundBound.equiv.trans continuedCompound.equiv
example : IsConic continuedCompound := continuedCompound.isConic

namespace Shadow

def Real.log (x : ℝ) : ℝ := x + 100

run_cmd do
  for (original, copied) in #[
      (``MorewTest.Reformulation.NegatedOccurrence.logSource, `sourceCopy),
      (``MorewTest.Reformulation.NegatedOccurrence.logBound, `boundCopy),
      (``MorewTest.Reformulation.NegatedOccurrence.compoundBound, `compoundCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported negated objective occurrence lost its presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))

example : sourceCopy = logSource := rfl
example : boundCopy = logBound := rfl
example : compoundCopy = compoundBound := rfl

end Shadow

end
end MorewTest.ImportCompatibility.NegatedOccurrence
