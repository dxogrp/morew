/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.Restrict

/-! # Restriction continuations and presentation reconstruction across imports -/

namespace MorewTest.Reformulation.ImportedRestrict

open Morew Restrict
noncomputable section

-- The imported presentation has normalized away `0 ≤ u²`. Explicitly adapt
-- the raw-pullback helper to this current problem, without weakening matching.
reformulation principalImported : ordinaryCoordinates := by
  restrict branch : 0 ≤ u using (by
    simpa only [ordinaryCoordinates, nonnegativeSource, Problem.pullback,
      Problem.addConstraint, sq_nonneg, true_and] using principalRepair)

example : GlobalEquiv ordinaryCoordinates principalImported := principalImported.equiv
example : principalImported = principalCoordinates := rfl

reformulation continued : successive := by
  restrict zero : x = 0 using (by
    refine { map := fun _ => ⟨0, ?_⟩, objective_le := ?_ }
    · change (|(0 : ℝ)| ≤ 1 ∧ 0 ≤ (0 : ℝ)) ∧ (0 : ℝ) = 0
      norm_num
    · intro point
      change (0 : ℝ) ^ 2 ≤ point.1 ^ 2
      simpa using sq_nonneg point.1)

example : GlobalEquiv squareLine continued := successive.equiv.trans continued.equiv
example (x : ℝ) : continued.feasible x ↔ |x| ≤ 1 ∧ 0 ≤ x ∧ x = 0 := Iff.rfl

section
variable (offset : ℝ)

reformulation continuedFamily : (shiftedRestricted offset) := by
  restrict upper : shifted ≤ 1 using (by
    refine { map := fun _ => ⟨-offset, ?_⟩, objective_le := ?_ }
    · change 0 ≤ -offset + offset ∧ -offset + offset ≤ 1
      simp
    · intro point
      change (-offset + offset) ^ 2 ≤ (point.1 + offset) ^ 2
      simpa using sq_nonneg (point.1 + offset))
  substitute x := u

example : GlobalEquiv (shiftedFamily offset) (continuedFamily offset) :=
  (shiftedRestricted.equiv offset).trans (continuedFamily.equiv offset)
example (u : ℝ) : (continuedFamily offset).feasible u ↔
    0 ≤ u + offset ∧ u + offset ≤ 1 := Iff.rfl
end

namespace Shadow
def branch (_ : ℝ) : Prop := False

reformulation renamed : Hygiene.target := by
  substitute x := u
  derive original_branch : Restrict.Hygiene.branch u using (by intro point hp; exact hp)

example : GlobalEquiv squareLine renamed := Hygiene.target.equiv.trans renamed.equiv
example (u : ℝ) : renamed.feasible u ↔
    Restrict.Hygiene.branch u ∧ Restrict.Hygiene.branch u := Iff.rfl

run_cmd do
  for (original, copied) in #[
      (``ordered, `orderedCopy), (``explicitRows, `rowsCopy),
      (``Hygiene.target, `hygienicCopy)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) original
      | Lean.throwError "imported restriction lost presentation metadata"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    Lean.Elab.Command.elabCommand (← `(noncomputable def $(Lean.mkIdent copied) := $term))
    let declaration ← Lean.getConstInfo ((← Lean.getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      Lean.throwError "restriction replay contains incomplete evidence"

example : orderedCopy = ordered := rfl
example : rowsCopy = explicitRows := rfl
example : hygienicCopy = Hygiene.target := rfl
end Shadow

end
end MorewTest.Reformulation.ImportedRestrict
