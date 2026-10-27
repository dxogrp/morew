/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Stable index names in targeted and terminal presentations -/

namespace MorewTest.Reformulation.IndexNames

open Morew
noncomputable section

section Symbolic

variable (n : ℕ)

def normBound :=
  problem (v : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to norm : ‖WithLp.toLp 2 v‖ ≤ t

reformulation normTargeted : (normBound n) := by
  nlp at norm

reformulation normTerminal : (normBound n) := by
  nlp

-- Terminal rendering retains the same generated index as targeted rendering.
/--
info: problem (v : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    norm_nlp_1 : 0 ≤ t
    norm_nlp_2 : ∑ i, v i ^ 2 ≤ t ^ 2
-/
#guard_msgs in
#printp normTargeted

/--
info: problem (v : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    norm_nlp_1 : 0 ≤ t
    norm_nlp_2 : ∑ i, v i ^ 2 ≤ t ^ 2
-/
#guard_msgs in
#printp normTerminal

example : GlobalEquivalence (normBound n) (normTerminal n) := normTerminal.equivalence n
example : (normTerminal.nlpForm n).data.toProblem = normTerminal n :=
  (normTerminal.nlpForm n).represents

end Symbolic

-- Preserve a user-written inner index while avoiding capture of decision `i`.
def nestedBound :=
  problem (i : ℝ) (v : Fin 2 → Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to
      norm : ‖WithLp.toLp 2 (fun row => ∑ column, v row column + i)‖ ≤ t

reformulation nestedTargeted : nestedBound := by
  nlp at norm

reformulation nestedTerminal : nestedBound := by
  nlp

/--
info: problem (i : ℝ) (v : Fin 2 → Fin 3 → ℝ) (t : ℝ)
  minimize t
  subject to
    norm_nlp_1 : 0 ≤ t
    norm_nlp_2 : ∑ i_1, (∑ column, v i_1 column + i) ^ 2 ≤ t ^ 2
-/
#guard_msgs in
#printp nestedTargeted

/--
info: problem (i : ℝ) (v : Fin 2 → Fin 3 → ℝ) (t : ℝ)
  minimize t
  subject to
    norm_nlp_1 : 0 ≤ t
    norm_nlp_2 : ∑ i_1, (∑ column, v i_1 column + i) ^ 2 ≤ t ^ 2
-/
#guard_msgs in
#printp nestedTerminal

example (i : ℝ) (v : Fin 2 → Fin 3 → ℝ) (t : ℝ) :
    nestedTerminal.feasible ((i, v), t) ↔
      0 ≤ t ∧ (∑ row, (∑ column, v row column + i) ^ 2) ≤ t ^ 2 := Iff.rfl
example : nestedTerminal.nlpForm.data.toProblem = nestedTerminal :=
  nestedTerminal.nlpForm.represents

end
end MorewTest.Reformulation.IndexNames
