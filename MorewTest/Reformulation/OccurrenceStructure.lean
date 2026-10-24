/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.OccurrenceStructure.Defined

/-!
# Direct occurrences survive presentation recovery

Selection counts the typed expression before beta or zeta reduction. Retaining
a model-local definition, applying a source family, and importing a generated
target must not duplicate or erase those direct occurrences.
-/

namespace MorewTest.Reformulation.OccurrenceStructure

open Morew
noncomputable section

def duplicated :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize (fun y : ℝ => y + y) loss

reformulation duplicatedLift : duplicated := by
  epigraph t at loss

example : GlobalEquivalence duplicated duplicatedLift := duplicatedLift.equivalence
example (x t : ℝ) : duplicatedLift.objective (x, t) = t + t := rfl
example (x t : ℝ) : duplicatedLift.feasible (x, t) ↔ x ^ 2 ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  let loss := x ^ 2
  minimize (fun y => y + y) t
  subject to
    epigraph_t : loss ≤ t
-/
#guard_msgs in
#printp duplicatedLift

-- Ambient printing options must not change the stored selector structure.
set_option pp.beta true in
reformulation ambientOptionLift : duplicated := by
  epigraph t at loss

example : ambientOptionLift = duplicatedLift := rfl

def control :=
  problem (x : ℝ)
    minimize (fun y : ℝ => y + y) (x ^ 2)

reformulation controlLift : control := by
  epigraph t at (x ^ 2)

def unusedDefinition :=
  problem (x : ℝ)
    let unused := x
    minimize (fun y : ℝ => y + y) (x ^ 2)

reformulation unusedDefinitionLift : unusedDefinition := by
  epigraph t at (x ^ 2)

example : GlobalEquivalence unusedDefinition unusedDefinitionLift :=
  unusedDefinitionLift.equivalence
example : unusedDefinitionLift = controlLift := rfl
example (x t : ℝ) : unusedDefinitionLift.objective (x, t) = t + t := rfl
example (x t : ℝ) : unusedDefinitionLift.feasible (x, t) ↔ x ^ 2 ≤ t := Iff.rfl

def positiveControl :=
  problem (x : ℝ)
    minimize (fun y : ℝ => y + y) (Real.log x)
    subject to
      positive : 0 < x

reformulation substitutedControl : positiveControl := by
  substitute x := Real.exp u

-- A definition-free substitution target must also retain direct occurrences.
reformulation substitutedControlLift : substitutedControl := by
  epigraph t at (u)

example : GlobalEquivalence substitutedControl substitutedControlLift :=
  substitutedControlLift.equivalence
example (u t : ℝ) : substitutedControlLift.objective (u, t) = t + t := rfl

def erased :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize (fun _ : ℝ => (0 : ℝ)) loss

reformulation erasedLift : erased := by
  epigraph t at loss

example : GlobalEquivalence erased erasedLift := erasedLift.equivalence
example (x t : ℝ) : erasedLift.objective (x, t) = 0 := rfl
example (x t : ℝ) : erasedLift.feasible (x, t) ↔ x ^ 2 ≤ t := Iff.rfl

def innerLet :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize let y := loss; y + y

reformulation innerLetLift : innerLet := by
  epigraph t at loss

example : GlobalEquivalence innerLet innerLetLift := innerLetLift.equivalence
example (x t : ℝ) : innerLetLift.objective (x, t) = t + t := rfl
example (x t : ℝ) : innerLetLift.feasible (x, t) ↔ x ^ 2 ≤ t := Iff.rfl

def constraint :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to
      cap : (fun y : ℝ => y + y ≤ 10) loss

reformulation constraintLift : constraint := by
  epigraph t at loss in cap

example : GlobalEquivalence constraint constraintLift := constraintLift.equivalence
example (x t : ℝ) : constraintLift.objective (x, t) = x := rfl
example (x t : ℝ) : constraintLift.feasible (x, t) ↔
    t + t ≤ 10 ∧ x ^ 2 ≤ t := Iff.rfl

-- The two direct references remain ambiguous, irrespective of lambda uses.
def repeated :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize (fun y : ℝ => y + y) loss + loss

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedLift : repeated := by
  epigraph t at loss

private def hiddenSquare (x : ℝ) : ℝ := x ^ 2

def hidden :=
  problem (x : ℝ)
    let unused := x
    minimize hiddenSquare x

-- Recovering local definitions still does not unfold unrelated helper bodies.
/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation hiddenLift : hidden := by
  epigraph t at (x ^ 2)

section

variable (offset : ℝ)

reformulation appliedLift : (Defined.family offset) := by
  epigraph t at loss

end

example (offset : ℝ) : GlobalEquivalence (Defined.family offset) (appliedLift offset) :=
  appliedLift.equivalence offset
example (offset x t : ℝ) : (appliedLift offset).objective (x, t) =
    (t + t) + (x - offset) ^ 2 := rfl
example (offset x t : ℝ) : (appliedLift offset).feasible (x, t) ↔
    (x - offset) ^ 2 + (x - offset) ^ 2 ≤ 10 ∧ (x - offset) ^ 2 ≤ t := Iff.rfl

-- Cross both a compiled module boundary and a generated declaration boundary.
reformulation generatedLift : (Defined.generated 2) := by
  epigraph t at loss

example : GlobalEquivalence (Defined.generated 2) generatedLift :=
  generatedLift.equivalence
example (x t : ℝ) : generatedLift.objective (x, t) =
    (t + t) + (x - 2) ^ 2 := rfl

-- The untouched constraint of a generated target keeps its single direct use.
reformulation continued : generatedLift := by
  epigraph s at loss in cap

example : GlobalEquivalence generatedLift continued := continued.equivalence
example (x t s : ℝ) : continued.objective ((x, t), s) =
    (t + t) + (x - 2) ^ 2 := rfl
example (x t s : ℝ) : continued.feasible ((x, t), s) ↔
    s + s ≤ 10 ∧ (x - 2) ^ 2 ≤ t ∧ (x - 2) ^ 2 ≤ s := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  for name in #[``appliedLift, ``generatedLift, ``continued] do
    let some view := Morew.Syntax.getProblemView? env name
      | Lean.throwError "occurrence recovery lost the target presentation"
    unless view.definitions.map (·.name.eraseMacroScopes) == #[`loss, `same, `unused] do
      Lean.throwError "occurrence recovery lost or reordered named definitions"

end
end MorewTest.Reformulation.OccurrenceStructure
