/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.LogDet.Sources

/-! Exact log-determinant bounds support both rewrite orders and explicit rule selection. -/

namespace MorewTest.Reformulation.LogDet

open Morew Morew.Conic

noncomputable section

variable (n : Nat) (hn : 0 < n)

reformulation terminal : (source n) := by conic

reformulation domainFirst : (source n) := by
  conic at domain
  conic at bound
  conic

reformulation logDetFirst : (source n) := by
  conic at bound
  conic at domain
  conic

reformulation namedRule : (source n) := by
  conic at bound using Morew.Conic.LogDet.hypograph
  conic

reformulation appliedRule : (source n) := by
  conic at bound using (Morew.Conic.LogDet.hypograph hn)
  conic

example : GlobalEquivalence (source n) (terminal n) := terminal.equivalence n hn
example : IsConic (terminal n) := terminal.isConic n
example : (terminal.conicForm n).data.rowCount = 4 := rfl
example : (terminal.conicForm n).data.toProblem = terminal n :=
  (terminal.conicForm n).represents
example : GlobalEquivalence (source n) (domainFirst n) := domainFirst.equivalence n hn
example : GlobalEquivalence (source n) (logDetFirst n) := logDetFirst.equivalence n hn
example : GlobalEquivalence (source n) (namedRule n) := namedRule.equivalence n hn
example : GlobalEquivalence (source n) (appliedRule n) := appliedRule.equivalence n hn

reformulation reverseTarget : (reverseSource n) := by conic
example : GlobalEquivalence (reverseSource n) (reverseTarget n) :=
  reverseTarget.equivalence n hn

end
end MorewTest.Reformulation.LogDet
