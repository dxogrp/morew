/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.NegatedOccurrence

/-! Conic continuations of objective bounds in decreasing contexts. -/

namespace MorewTest.Reformulation.NegatedOccurrence
open Morew
noncomputable section

reformulation logConic : logBound := by conic

example : GlobalEquiv logSource logConic :=
  logBound.equiv.trans logConic.equiv
example : IsConic logConic := logConic.isConic
example : logConic.conicForm.data.toProblem = logConic := logConic.conicForm.represents

reformulation absConic : absBound := by conic

example : IsConic absConic := absConic.isConic
example : absConic.conicForm.data.sense = .maximize := rfl

reformulation compoundConic : compoundBound := by conic

example : GlobalEquiv compoundSource compoundConic :=
  compoundBound.equiv.trans compoundConic.equiv
example : IsConic compoundConic := compoundConic.isConic
example : compoundConic.conicForm.data.rowCount = 4 := rfl

end
end MorewTest.Reformulation.NegatedOccurrence
