import MorewTest.ImportCompatibility.LocalDefinitions.Defined

/-!
# Occurrence selectors after importing model-local definitions

Applied parameters, external helper resolution, and local binding identities
must survive compiled source and generated declarations.
-/

namespace MorewTest.ImportCompatibility.OccurrenceBounds

open Morew
noncomputable section

-- This same spelling must not capture the helper resolved by the source module.
def score (offset x : ℝ) : ℝ := offset + x

reformulation constraintLift : (LocalDefinitions.Defined.family 2) := by
  epigraph t at loss in cap as loss_bound

example : GlobalEquivalence (LocalDefinitions.Defined.family 2) constraintLift :=
  constraintLift.equivalence

example (x t : ℝ) : constraintLift.objective (x, t) =
    LocalDefinitions.Defined.External.score 2 x +
      LocalDefinitions.Defined.External.score 2 x := rfl

example (x t : ℝ) : constraintLift.feasible (x, t) ↔
    t ≤ 10 ∧ LocalDefinitions.Defined.External.score 2 x ≤ t := Iff.rfl

reformulation objectiveLift : (LocalDefinitions.Defined.family 3) := by
  epigraph t at total

example (x t : ℝ) : objectiveLift.feasible (x, t) ↔
    LocalDefinitions.Defined.External.score 3 x ≤ 10 ∧
      LocalDefinitions.Defined.External.score 3 x +
        LocalDefinitions.Defined.External.score 3 x ≤ t := Iff.rfl

reformulation generatedLift : (LocalDefinitions.Defined.generated 4) := by
  epigraph s at loss in cap

example : GlobalEquivalence (LocalDefinitions.Defined.generated 4) generatedLift :=
  generatedLift.equivalence

example (x t s : ℝ) : generatedLift.feasible ((x, t), s) ↔
    s ≤ 10 ∧ (LocalDefinitions.Defined.External.score 4 x +
      LocalDefinitions.Defined.External.score 4 x ≤ t) ∧
        LocalDefinitions.Defined.External.score 4 x ≤ s := Iff.rfl

run_cmd do
  for name in #[``constraintLift, ``objectiveLift, ``generatedLift] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "occurrence lift lost imported local definitions"
    unless view.definitions.map (·.name.eraseMacroScopes) == #[`loss, `same, `total, `unused] do
      Lean.throwError "occurrence lift changed imported binding identity or order"

end
end MorewTest.ImportCompatibility.OccurrenceBounds
