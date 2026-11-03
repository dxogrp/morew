/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.DeriveBackends

/-! # Imported derived constraints retain their meanings and presentation -/

namespace MorewTest.Reformulation.ImportedDerive

open Morew Derive
noncomputable section

reformulation continuedMaximum : withMargin := by
  derive positive : 0 < x using (by
    intro point hp
    exact lt_of_lt_of_le zero_lt_one hp.2.2)
  substitute x := Real.exp u

example : GlobalEquivalence transitiveSource continuedMaximum :=
  withMargin.equivalence.trans continuedMaximum.equivalence
example : continuedMaximum = exponential := rfl

reformulation continuedMinimum : afterEpigraph := by
  derive copied_bound : x ^ 2 ≤ t using (by intro point hp; exact hp.1)

example : GlobalEquivalence quadratic continuedMinimum :=
  afterEpigraph.equivalence.trans continuedMinimum.equivalence
example (x t : ℝ) : continuedMinimum.feasible (x, t) ↔
    x ^ 2 ≤ t ∧ x ^ 2 ≤ t + 1 ∧ x ^ 2 ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    objective_bound : x ^ 2 ≤ t
    relaxed_bound : x ^ 2 ≤ t + 1
    copied_bound : x ^ 2 ≤ t
-/
#guard_msgs in
#printp continuedMinimum

section
variable (offset : ℝ)

reformulation continuedFamily : (shiftedDerived offset) := by
  derive repeated_lower : 0 ≤ shifted using (by intro point hp; exact hp.1)
  substitute x := u

example : GlobalEquivalence (shiftedFamily offset) (continuedFamily offset) :=
  (shiftedDerived.equivalence offset).trans (continuedFamily.equivalence offset)
example (u : ℝ) : (continuedFamily offset).feasible u ↔
    0 ≤ u + offset ∧ 0 ≤ (u + offset) + (u + offset) ∧ 0 ≤ u + offset := Iff.rfl
end

section
variable (auxiliary_aux auxiliary_aux_1 : ℝ)

-- Freshening against parameters introduced by derive permits ordinary imported
-- continuation using those same parameters.
reformulation continuedAuxiliary : (freshenedAuxiliary auxiliary_aux auxiliary_aux_1) := by
  derive square : 0 ≤ auxiliary_aux_2 ^ 2 using (by
    intro point _
    exact sq_nonneg point.2)

example : GlobalEquivalence SecondOrderCustom.source
    (continuedAuxiliary auxiliary_aux auxiliary_aux_1) :=
  (freshenedAuxiliary.equivalence auxiliary_aux auxiliary_aux_1).trans
    (continuedAuxiliary.equivalence auxiliary_aux auxiliary_aux_1)
end

namespace Shadow

def cap (_ : ℝ) : Prop := False

reformulation renamed : Hygiene.target := by
  substitute x := u
  derive original_cap : Derive.Hygiene.cap u using (by intro point hp; exact hp.1)

example (u : ℝ) : renamed.feasible u ↔
    Derive.Hygiene.cap u ∧ Derive.Hygiene.cap u ∧ Derive.Hygiene.cap u := Iff.rfl
example : GlobalEquivalence Hygiene.source renamed :=
  Hygiene.target.equivalence.trans renamed.equivalence

run_cmd do
  for (original, copied) in #[
      (``withMargin, `marginCopy), (``continuedMinimum, `minimumCopy),
      (``Hygiene.target, `hygienicCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported derivation lost presentation metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "derived-constraint replay contains incomplete evidence"

example : marginCopy = withMargin := rfl
example : minimumCopy = continuedMinimum := rfl
example : hygienicCopy = Hygiene.target := rfl

end Shadow

end
end MorewTest.Reformulation.ImportedDerive
