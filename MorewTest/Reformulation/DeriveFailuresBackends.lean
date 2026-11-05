/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.DeriveFailures

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.DeriveFailures

open Morew
noncomputable section

#guard_error_fragments ["terminal"] in
assert_derive_atomic% afterTerminal afterTerminalAlias in
reformulation afterTerminal : unrestricted certificate afterTerminalAlias := by
  conic
  derive self : x ≤ x using selfBound

#guard_error_fragments ["disjunction"] in
assert_derive_atomic% unsupportedConic unsupportedConicAlias in
reformulation unsupportedConic : unrestricted certificate unsupportedConicAlias := by
  derive disjunction : x ≤ 0 ∨ 0 ≤ x using (fun point _ => le_total point 0)
  conic

#guard_error_fragments ["disjunction"] in
assert_derive_atomic% unsupportedNLP unsupportedNLPAlias in
reformulation unsupportedNLP : unrestricted certificate unsupportedNLPAlias := by
  derive disjunction : x ≤ 0 ∨ 0 ≤ x using (fun point _ => le_total point 0)
  nlp

end
end MorewTest.Reformulation.DeriveFailures
