/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ImportCompatibility.Exponential.Defined

/-!
# Imported exponential presentations and certificates

Quantified EXP rows and section-local domain evidence survive compilation and
subsequent transformations. Re-elaboration under shadowing declarations must
retain the original dimension and margin names.
-/

namespace MorewTest.ImportCompatibility.Exponential

open Morew Morew.Conic
noncomputable section

variable [Parameter] (hn : 0 < Parameter.size) (hε : 0 < Parameter.epsilon)

/--
info: problem (v : Fin Parameter.size → ℝ) (y t : ℝ) (lse_aux : Fin Parameter.size → ℝ)
  minimize t
  subject to
    lse_conic_1 : ∀ (i : Fin Parameter.size), (v i - t, 1, lse_aux i) ∈ EXP
    lse_conic_2 : ∑ i, lse_aux i ≤ 1
    margin : Parameter.epsilon ≤ y
    logarithm_conic_1 : (t, 1, y) ∈ EXP
    remaining : |t| ≤ 5
-/
#guard_msgs in
#printp lowered

reformulation continued : lowered := by
  conic at remaining
  epigraph value as objectiveBound

/--
info: problem (v : Fin Parameter.size → ℝ) (y t : ℝ) (lse_aux : Fin Parameter.size → ℝ) (value : ℝ)
  minimize value
  subject to
    lse_conic_1 : ∀ (i : Fin Parameter.size), (v i - t, 1, lse_aux i) ∈ EXP
    lse_conic_2 : ∑ i, lse_aux i ≤ 1
    margin : Parameter.epsilon ≤ y
    logarithm_conic_1 : (t, 1, y) ∈ EXP
    remaining_conic_1 : t ≤ 5
    remaining_conic_2 : -t ≤ 5
    objectiveBound : t ≤ value
-/
#guard_msgs in
#printp continued

example : GlobalEquivalence lowered continued := continued.equivalence

example : GlobalEquivalence source continued :=
  (lowered.equivalence hn hε).trans continued.equivalence

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ)
    (value : ℝ) : continued.objective ((((v, y), t), u), value) = value := rfl

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ)
    (value : ℝ) : continued.feasible ((((v, y), t), u), value) ↔
      (∀ i, (v i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 ∧
        Parameter.epsilon ≤ y ∧ (t, 1, y) ∈ EXP ∧
        t ≤ 5 ∧ -t ≤ 5 ∧ t ≤ value := Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  let some imported := Morew.Syntax.getProblemView? env ``lowered
    | Lean.throwError "import lost the exponential presentation"
  let some composed := Morew.Syntax.getProblemView? env ``continued
    | Lean.throwError "composition lost the exponential presentation"
  let importedNames := imported.constraints.map (·.name)
  let composedNames := composed.constraints.map (·.name)
  unless importedNames == #[`lse_conic_1, `lse_conic_2, `margin,
      `logarithm_conic_1, `remaining] do
    Lean.throwError "import changed exponential labels or row order: {importedNames}"
  unless composedNames == #[`lse_conic_1, `lse_conic_2, `margin, `logarithm_conic_1,
      `remaining_conic_1, `remaining_conic_2, `objectiveBound] do
    Lean.throwError "composition changed exponential labels or row order: {composedNames}"

namespace Shadow

def Parameter.size : Nat := 37

def Parameter.epsilon : ℝ := 100

run_cmd do
  for (source, copied) in #[(``lowered, `copiedLowered), (``continued, `copiedContinued)] do
    let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) source
      | Lean.throwError "import lost the exponential presentation: {source}"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copied
    Lean.Elab.Command.elabCommand (← `(def $name := $term))

end Shadow

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ) :
    Shadow.copiedLowered.objective (((v, y), t), u) =
      lowered.objective (((v, y), t), u) := rfl

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ) :
    Shadow.copiedLowered.feasible (((v, y), t), u) ↔
      lowered.feasible (((v, y), t), u) := Iff.rfl

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ)
    (value : ℝ) : Shadow.copiedContinued.objective ((((v, y), t), u), value) =
      continued.objective ((((v, y), t), u), value) := rfl

example (v : Fin Parameter.size → ℝ) (y t : ℝ) (u : Fin Parameter.size → ℝ)
    (value : ℝ) : Shadow.copiedContinued.feasible ((((v, y), t), u), value) ↔
      continued.feasible ((((v, y), t), u), value) := Iff.rfl

end
end MorewTest.ImportCompatibility.Exponential
