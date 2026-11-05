/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.TerminalNLPFailures

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.TerminalNLPFailures

open Morew
noncomputable section

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_nlp_terminal_atomic%
reformulation conicAfterTerminal : smoothSource := by
  nlp
  conic

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_nlp_terminal_atomic%
reformulation nlpAfterConic : smoothSource := by
  epigraph t
  conic
  nlp

end
end MorewTest.Reformulation.TerminalNLPFailures
