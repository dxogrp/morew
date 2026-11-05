/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.RestrictFailures

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.RestrictFailures

open Morew
noncomputable section

#guard_error_fragments ["unknown or stale constraint label", "domain"] in
assert_restrict_atomic% removedLabel removedLabelAlias in
reformulation removedLabel : squareLine certificate removedLabelAlias := by
  restrict domain : 0 ≤ x using zeroRepair
  substitute x := u ^ 2
  conic at domain

#guard_error_fragments ["terminal"] in
assert_restrict_atomic% afterTerminal afterTerminalAlias in
reformulation afterTerminal : free certificate afterTerminalAlias := by
  conic
  restrict tag : True using trueRepair free

-- A valid restriction does not exempt its predicate from target admission rules.
def disjunctionRepair :
    GlobalImprovement free (free.addConstraint (fun x => x ≤ 0 ∨ 0 ≤ x)) where
  map point := ⟨point.1, point.2, le_total point.1 0⟩
  objective_le _ := le_rfl

#guard_error_fragments ["constraint `signs`", "no supported"] in
assert_restrict_atomic% unsupportedConic unsupportedConicAlias in
reformulation unsupportedConic : free certificate unsupportedConicAlias := by
  restrict signs : x ≤ 0 ∨ 0 ≤ x using disjunctionRepair
  conic

#guard_error_fragments ["constraint `signs`", "not certified"] in
assert_restrict_atomic% unsupportedNLP unsupportedNLPAlias in
reformulation unsupportedNLP : free certificate unsupportedNLPAlias := by
  restrict signs : x ≤ 0 ∨ 0 ≤ x using disjunctionRepair
  nlp

end
end MorewTest.Reformulation.RestrictFailures
