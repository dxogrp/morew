/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ImportCompatibility.TerminalQuadConic.Defined

/-! Imported quadratic certificates retain the correct direction and proof parameters. -/

namespace MorewTest.ImportCompatibility.TerminalQuadConic

open Morew
noncomputable section

variable (weight ε : ℝ) (hweight : 0 ≤ weight) (hε : 0 < ε)

def importedForm : QuadConic.Form (target weight ε) :=
  target.quadConicForm weight ε hweight

example : (importedForm weight ε hweight).data.toProblem = target weight ε :=
  (importedForm weight ε hweight).represents
example : (importedForm weight ε hweight).data.sense = .minimize := rfl
example : IsQuadConic (target weight ε) := target.isQuadConic weight ε hweight
example : GlobalEquiv (source weight ε) (target weight ε) := target.equiv weight ε hε
example : IsQuadConic (maximumTarget weight) := maximumTarget.isQuadConic weight hweight
example : (maximumTarget.quadConicForm weight hweight).data.sense = .maximize := rfl
example : GlobalEquiv (maximum weight) (maximumTarget weight) := maximumTarget.equiv weight

include hweight in
reformulation continued : (maximumTarget weight) := by
  qconic
example : GlobalEquiv (maximum weight) (continued weight) :=
  (maximumTarget.equiv weight).trans (continued.equiv weight)
example : IsQuadConic (continued weight) := continued.isQuadConic weight hweight

end
end MorewTest.ImportCompatibility.TerminalQuadConic
