import MorewTest.ImportCompatibility.SecondOrder.Defined

/-!
# Imported second-order presentations and certificates

An imported conditional quotient certificate composes with another conic step
and an epigraph. Compact cone notation, section parameters, and every
retained/generated row survive the compiled module boundary. Stored presentations
also re-elaborate under shadowing names without changing their meaning.
-/

namespace MorewTest.ImportCompatibility.SecondOrder

open Morew Morew.Conic
noncomputable section

variable [Parameter]

/--
info: problem (v : Fin Parameter.size → ℝ) (x y t : ℝ)
  minimize t
  subject to
    norm_conic_1 : (t, v) ∈ SOC Parameter.size
    margin : 1 / 2 ≤ y
    quotient_conic_1 : (t, y / 2, ![x - Parameter.offset]) ∈ RSOC 1
    remaining : |x| ≤ 5
-/
#guard_msgs in
#printp lowered

reformulation continued : lowered := by
  conic at remaining
  epigraph value as objectiveBound

/--
info: problem (v : Fin Parameter.size → ℝ) (x y t value : ℝ)
  minimize value
  subject to
    norm_conic_1 : (t, v) ∈ SOC Parameter.size
    margin : 1 / 2 ≤ y
    quotient_conic_1 : (t, y / 2, ![x - Parameter.offset]) ∈ RSOC 1
    remaining_conic_1 : x ≤ 5
    remaining_conic_2 : -x ≤ 5
    objectiveBound : t ≤ value
-/
#guard_msgs in
#printp continued

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
  let some imported := Morew.Syntax.getProblemView? env ``lowered
    | Lean.throwError "import lost the second-order presentation"
  let some composed := Morew.Syntax.getProblemView? env ``continued
    | Lean.throwError "composition lost the second-order presentation"
  let importedNames := imported.constraints.map (·.name)
  let composedNames := composed.constraints.map (·.name)
  unless importedNames == #[`norm_conic_1, `margin, `quotient_conic_1, `remaining] do
    Lean.throwError "import changed cone labels or row order: {importedNames}"
  unless composedNames == #[`norm_conic_1, `margin, `quotient_conic_1,
      `remaining_conic_1, `remaining_conic_2, `objectiveBound] do
    Lean.throwError "composition changed cone labels or row order: {composedNames}"

namespace Shadow

def Parameter.size : Nat := 37

def Parameter.offset : ℝ := 100

run_cmd do
  for (source, copied) in #[(``lowered, `copiedLowered), (``continued, `copiedContinued)] do
    let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) source
      | Lean.throwError "import lost the second-order presentation: {source}"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copied
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

end Shadow

-- These comparisons require the imported dimension and coefficient, not the
-- consumer's same-spelled declarations, and kernel-check the cone notation.
example (v : Fin Parameter.size → ℝ) (x y t : ℝ) :
    Shadow.copiedLowered.objective (((v, x), y), t) =
      lowered.objective (((v, x), y), t) := rfl

example (v : Fin Parameter.size → ℝ) (x y t : ℝ) :
    Shadow.copiedLowered.feasible (((v, x), y), t) ↔
      lowered.feasible (((v, x), y), t) := Iff.rfl

example (v : Fin Parameter.size → ℝ) (x y t value : ℝ) :
    Shadow.copiedContinued.objective ((((v, x), y), t), value) =
      continued.objective ((((v, x), y), t), value) := rfl

example (v : Fin Parameter.size → ℝ) (x y t value : ℝ) :
    Shadow.copiedContinued.feasible ((((v, x), y), t), value) ↔
      continued.feasible ((((v, x), y), t), value) := Iff.rfl

end
end MorewTest.ImportCompatibility.SecondOrder
