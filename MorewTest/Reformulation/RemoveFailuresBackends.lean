/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.RemoveFailures

/-! Backend integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.RemoveFailures

open Morew
noncomputable section

def absolute :=
  problem (x : ℝ)
    minimize x
    subject to magnitude : |x| ≤ 1

-- Helpers and metadata from successful prior steps must roll back with a late failure.
#guard_error_fragments ["constraint", "magnitude_conic_2", "using"] in
assert_remove_atomic% lateFailure lateFailureAlias in
reformulation lateFailure : absolute certificate lateFailureAlias := by
  conic at magnitude
  derive tag : True using (fun _ _ => True.intro)
  remove at tag
  remove at magnitude_conic_2

#guard_error_fragments ["cannot apply a reformulation step after a terminal step"] in
assert_remove_atomic% afterConic afterConicAlias in
reformulation afterConic : duplicate certificate afterConicAlias := by
  conic
  remove at first

#guard_error_fragments ["cannot apply a reformulation step after a terminal step"] in
assert_remove_atomic% afterNLP afterNLPAlias in
reformulation afterNLP : duplicate certificate afterNLPAlias := by
  nlp
  remove at first

reformulation lateFailure : absolute certificate lateFailureAlias := by
  derive temporary : True using (by intro _ _; trivial)
  remove at temporary

example : lateFailure = absolute := rfl
example : GlobalEquivalence absolute lateFailure := lateFailureAlias

end
end MorewTest.Reformulation.RemoveFailures
