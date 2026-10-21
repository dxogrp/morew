import PTranTest.ImportCompatibility.SecondOrder.Defined

/-!
# Imported second-order presentations and certificates

An imported conditional quotient certificate composes with another conic step
and an epigraph. The section parameters and every retained/generated row survive
the compiled module boundary.
-/

namespace PTranTest.ImportCompatibility.SecondOrder

open PTran PTran.Conic
noncomputable section

variable [Parameter]

reformulation continued : lowered := by
  conic at remaining
  epigraph value as objectiveBound

example : GlobalEquivalence lowered continued := continued.equivalence

example : GlobalEquivalence source continued :=
  lowered.equivalence.trans continued.equivalence

example (v : Fin Parameter.size → ℝ) (x y t value : ℝ) :
    continued.objective ((((v, x), y), t), value) = value := rfl

example (v : Fin Parameter.size → ℝ) (x y t value : ℝ) :
    continued.feasible ((((v, x), y), t), value) ↔
      (t, v) ∈ (Cone.secondOrder Parameter.size).carrier ∧ 1 / 2 ≤ y ∧
        (t, y / 2, ![x - Parameter.offset]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
        x ≤ 5 ∧ -x ≤ 5 ∧ t ≤ value := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  let some imported := PTran.Syntax.getProblemView? env ``lowered
    | Lean.throwError "import lost the second-order presentation"
  let some composed := PTran.Syntax.getProblemView? env ``continued
    | Lean.throwError "composition lost the second-order presentation"
  let importedNames := imported.constraints.map (·.name)
  let composedNames := composed.constraints.map (·.name)
  unless importedNames == #[`norm_conic_1, `margin, `quotient_conic_1, `remaining] do
    Lean.throwError "import changed cone labels or row order: {importedNames}"
  unless composedNames == #[`norm_conic_1, `margin, `quotient_conic_1,
      `remaining_conic_1, `remaining_conic_2, `objectiveBound] do
    Lean.throwError "composition changed cone labels or row order: {composedNames}"

end
end PTranTest.ImportCompatibility.SecondOrder
