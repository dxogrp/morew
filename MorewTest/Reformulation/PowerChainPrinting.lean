/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.PowerPrinting
import MorewTest.Reformulation.PowerFamilies
import MorewTest.Reformulation.PrintDetails

/-!
# Mathematical chain output and ordinary detailed inspection

The existing chain fixtures supply concrete, singleton, symbolic, targeted, and
terminal models. Targeted snapshots live in PowerPrinting; terminal snapshots
below complete the dimension matrix. The command checks also exercise print-time
selection without replacing either stored replay view.
-/

namespace MorewTest.Reformulation.PowerChainPrinting

open Lean Lean.Elab.Command Morew
open MorewTest.Reformulation.PrintDetails (printed)

/-- Exercise the real command and ensure mathematical output is print-only. -/
def checkMathematical (declaration : Name) (required : Array String := #[]) :
    CommandElabM Unit := do
  let compact ← printed declaration false
  let detailed ← printed declaration true
  let compactAgain ← printed declaration false
  unless compact == compactAgain do
    throwError "detailed inspection changed subsequent mathematical output"
  unless compact.contains "-- Mathematical view" && compact.contains "[0]" &&
      compact.contains "[j + 1]" && compact.contains "∀ j : ℕ, j <" do
    throwError "a complete power chain did not receive mathematical output: {compact}"
  if compact.contains "⋯" || compact.contains "_proof_" then
    throwError "mathematical chain output leaked proof scaffolding: {compact}"
  unless !detailed.contains "-- Mathematical view" && !detailed.contains "[j + 1]" &&
      detailed.contains "⟨" && detailed.contains "POW" do
    throwError "pp.proofs did not restore ordinary finite-index syntax: {detailed}"
  for fragment in required do
    unless compact.contains fragment do
      throwError "mathematical output lost {fragment}: {compact}"
  let environment ← getEnv
  for view? in #[Syntax.getProblemView? environment declaration,
      Syntax.getProblemDisplayView? environment declaration] do
    let some view := view? | throwError "mathematical printing lost a stored syntax view"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let text := (← liftCoreM <| PrettyPrinter.ppTerm ⟨term⟩).pretty
    if text.contains "-- Mathematical view" || text.contains "[j + 1]" then
      throwError "mathematical coordinates entered stored replay syntax"

run_cmd do
  for declaration in #[``PowerPrinting.GeometricMean.singleton, ``PowerPrinting.GeometricMean.triple,
      ``PowerPrinting.GeometricMean.targeted, ``PowerPrinting.GeometricMean.ready,
      ``PowerPrinting.InverseProduct.singleton, ``PowerPrinting.InverseProduct.triple,
      ``PowerPrinting.InverseProduct.targeted, ``PowerPrinting.InverseProduct.ready,
      ``PowerFamilies.GeometricMean.singleton, ``PowerFamilies.GeometricMean.triple,
      ``PowerFamilies.InverseProduct.singleton, ``PowerFamilies.InverseProduct.triple] do
    checkMathematical declaration #["POW ((j + 1) / (j + 2))"]
  checkMathematical ``PowerPrinting.GeometricMean.targeted
    #["mean_aux[0] = x[0]", "j < n - 1", "0 ≤ mean_aux[n - 1]", "t ≤ mean_aux[n - 1]"]
  checkMathematical ``PowerPrinting.GeometricMean.ready
    #["mean_aux[0] - x[0] ∈ ({0} : Set ℝ)", "mean_aux[n - 1] - t ∈ ℝ₊"]
  checkMathematical ``PowerPrinting.InverseProduct.targeted #["POW (1 / (n + 1))"]
  checkMathematical ``PowerPrinting.InverseProduct.triple #["POW (1 / 4)"]
  checkMathematical ``PowerPrinting.InverseProduct.singleton #["POW (1 / 2)"]
  for source in #[``PowerPrinting.GeometricMean.source, ``PowerPrinting.InverseProduct.source] do
    let compact ← printed source false
    unless compact == (← printed source true) && !compact.contains "-- Mathematical view" &&
        !compact.contains "[0]" do
      throwError "chain formatting changed an original source presentation"

/--
info: -- Mathematical view
problem (x : Fin 1 → ℝ) (t : ℝ) (mean_aux : Fin 1 → ℝ)
  maximize t
  subject to
    domain : x ∈ ℝ₊^1
    mean_conic_1 : mean_aux[0] - x[0] ∈ ({0} : Set ℝ)
    mean_conic_2 : ∀ j : ℕ, j < 1 - 1 ⇒ (mean_aux[j], x[j + 1], mean_aux[j + 1]) ∈ POW ((j + 1) / (j + 2))
    mean_conic_3 : mean_aux[1 - 1] ∈ ℝ₊
    mean_conic_4 : mean_aux[1 - 1] - t ∈ ℝ₊
-/
#guard_msgs in
#printp PowerFamilies.GeometricMean.singleton

/--
info: -- Mathematical view
problem (x : Fin 3 → ℝ) (t : ℝ) (mean_aux : Fin 3 → ℝ)
  maximize t
  subject to
    domain : x ∈ ℝ₊^3
    mean_conic_1 : mean_aux[0] - x[0] ∈ ({0} : Set ℝ)
    mean_conic_2 : ∀ j : ℕ, j < 3 - 1 ⇒ (mean_aux[j], x[j + 1], mean_aux[j + 1]) ∈ POW ((j + 1) / (j + 2))
    mean_conic_3 : mean_aux[3 - 1] ∈ ℝ₊
    mean_conic_4 : mean_aux[3 - 1] - t ∈ ℝ₊
-/
#guard_msgs in
#printp PowerFamilies.GeometricMean.triple

/--
info: -- Mathematical view
problem (x : Fin n → ℝ) (t : ℝ) (mean_aux : Fin n → ℝ)
  maximize t
  subject to
    domain : x ∈ ℝ₊^n
    mean_conic_1 : mean_aux[0] - x[0] ∈ ({0} : Set ℝ)
    mean_conic_2 : ∀ j : ℕ, j < n - 1 ⇒ (mean_aux[j], x[j + 1], mean_aux[j + 1]) ∈ POW ((j + 1) / (j + 2))
    mean_conic_3 : mean_aux[n - 1] ∈ ℝ₊
    mean_conic_4 : mean_aux[n - 1] - t ∈ ℝ₊
-/
#guard_msgs in
#printp PowerPrinting.GeometricMean.ready

/--
info: -- Mathematical view
problem (x : Fin 1 → ℝ) (t : ℝ) (inverse_aux : Fin 1 → ℝ)
  minimize t
  subject to
    domain : (x - fun x => 1) ∈ ℝ₊^1
    inverse_conic_1 : inverse_aux[0] - x[0] ∈ ({0} : Set ℝ)
    inverse_conic_2 : ∀ j : ℕ, j < 1 - 1 ⇒ (inverse_aux[j], x[j + 1], inverse_aux[j + 1]) ∈ POW ((j + 1) / (j + 2))
    inverse_conic_3 : (t, inverse_aux[1 - 1], 1) ∈ POW (1 / 2)
-/
#guard_msgs in
#printp PowerFamilies.InverseProduct.singleton

/--
info: -- Mathematical view
problem (x : Fin 3 → ℝ) (t : ℝ) (inverse_aux : Fin 3 → ℝ)
  minimize t
  subject to
    domain : (x - fun x => 1) ∈ ℝ₊^3
    inverse_conic_1 : inverse_aux[0] - x[0] ∈ ({0} : Set ℝ)
    inverse_conic_2 : ∀ j : ℕ, j < 3 - 1 ⇒ (inverse_aux[j], x[j + 1], inverse_aux[j + 1]) ∈ POW ((j + 1) / (j + 2))
    inverse_conic_3 : (t, inverse_aux[3 - 1], 1) ∈ POW (1 / 4)
-/
#guard_msgs in
#printp PowerFamilies.InverseProduct.triple

/--
info: -- Mathematical view
problem (x : Fin n → ℝ) (t : ℝ) (inverse_aux : Fin n → ℝ)
  minimize t
  subject to
    domain : (x - fun x => 1) ∈ ℝ₊^n
    inverse_conic_1 : inverse_aux[0] - x[0] ∈ ({0} : Set ℝ)
    inverse_conic_2 : ∀ j : ℕ, j < n - 1 ⇒ (inverse_aux[j], x[j + 1], inverse_aux[j + 1]) ∈ POW ((j + 1) / (j + 2))
    inverse_conic_3 : (t, inverse_aux[n - 1], 1) ∈ POW (1 / (n + 1))
-/
#guard_msgs in
#printp PowerPrinting.InverseProduct.ready

noncomputable section

set_option pp.proofs true in
reformulation registeredDetailed : (PowerPrinting.GeometricMean.source 3) := by
  conic at mean

run_cmd do
  checkMathematical ``registeredDetailed
  unless (← printed ``registeredDetailed false) ==
      (← printed ``PowerPrinting.GeometricMean.triple false) do
    throwError "creation-time proof options changed mathematical chain output"
  for (getter, name) in #[(Syntax.getProblemView?, `exactReplay),
      (Syntax.getProblemDisplayView?, `displayReplay)] do
    let some view := getter (← getEnv) ``registeredDetailed
      | throwError "missing detailed chain replay view"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(noncomputable def $(mkIdent name) := $term))
    let declaration ← getConstInfo ((← getCurrNamespace) ++ name)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      throwError "chain replay contains unresolved terms or placeholders"

example : exactReplay = registeredDetailed := rfl
example : displayReplay = registeredDetailed := rfl

-- A product projection is a compound vector base that must be parenthesized
-- before mathematical indexing. It remains an ordinary affine decision map.
def projectedSource :=
  problem (bundle : (Fin 3 → ℝ) × ℝ) (t : ℝ)
    maximize t
    subject to
      domain : 0 ≤ bundle.1
      floorRow : t ≤ Fn.geoMean bundle.1

reformulation projected : projectedSource := by conic at floorRow

run_cmd do
  checkMathematical ``projected
    #["floorRow_aux[0] = (bundle.1)[0]", "(bundle.1)[j + 1]"]

set_option format.width 40 in
run_cmd do
  checkMathematical ``projected
    #["floorRow_aux[0] = (bundle.1)[0]", "(bundle.1)[j + 1]"]

example : GlobalEquivalence projectedSource projected := projected.equivalence

-- A natural subtraction inside a dimension must be evaluated before its result
-- enters the real-valued exponent. Retain that cast in the mathematical view.
def compoundSource (n m : ℕ) :=
  problem (x : Fin (n - m + 3) → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : (fun _ => (1 : ℝ)) ≤ x
      inverse : Fn.invProd x ≤ t

variable (n m : ℕ)

reformulation compound : (compoundSource n m) := by conic at inverse
reformulation compoundReady : (compound n m) := by conic

run_cmd do
  for declaration in #[``compound, ``compoundReady] do
    checkMathematical declaration #["Fin (n - m + 3)",
      "POW (1 / ((↑(n - m + 3) : ℝ) + 1))"]

example : (1 / ((((0 : ℕ) - 2 + 3 : ℕ) : ℝ) + 1) : ℝ) = 1 / 4 := by norm_num
example : (1 / ((0 : ℝ) - 2 + 3 + 1) : ℝ) = 1 / 2 := by norm_num
example : GlobalEquivalence (compoundSource n m) (compoundReady n m) :=
  (compound.equivalence n m).trans (compoundReady.equivalence n m)
example : (compoundReady.conicForm n m).data.toProblem = compoundReady n m :=
  (compoundReady.conicForm n m).represents

end
end MorewTest.Reformulation.PowerChainPrinting
