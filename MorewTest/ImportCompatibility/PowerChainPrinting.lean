/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ImportCompatibility.PowerChainPrinting.Defined
import MorewTest.Reformulation.PowerChainPrinting

/-!
# Imported mathematical chains after specialization and continuation

Two independently named chains survive the module boundary, concrete parameter
application, unrelated row conversion, and terminal certification.
-/

namespace MorewTest.ImportCompatibility.PowerChainPrinting

open Lean Lean.Elab.Command Morew
open MorewTest.Reformulation.PrintDetails (printed)
open MorewTest.Reformulation.PowerChainPrinting (checkMathematical)
noncomputable section

reformulation specialized : (Defined.lowered 3 (by decide)) := by
  conic at remaining

reformulation ready : specialized := by conic

run_cmd do
  for declaration in #[``Defined.lowered, ``Defined.registeredDetailed,
      ``specialized, ``ready] do
    checkMathematical declaration
      #["floorRow_aux[0]", "ceilingRow_aux[0]", "floorRow_conic_2", "ceilingRow_conic_2", "budget"]
  unless (← printed ``Defined.lowered false) == (← printed ``Defined.registeredDetailed false) do
    throwError "producer proof options changed imported mathematical output"
  let specialized ← printed ``specialized false
  for fragment in #["remaining_conic_1", "remaining_conic_2", "budget : ∑ i, x i ≤ 10"] do
    unless specialized.contains fragment do
      throwError "chain rendering changed an unrelated retained or converted row: {specialized}"
  let some view := Syntax.getProblemView? (← getEnv) ``specialized
    | throwError "missing specialized replay view"
  let labels := view.constraints.map (·.name.eraseMacroScopes)
  unless labels == #[`domain, `floorRow_conic_1, `floorRow_conic_2, `floorRow_conic_3,
      `floorRow_conic_4, `ceilingRow_conic_1, `ceilingRow_conic_2, `ceilingRow_conic_3,
      `budget, `remaining_conic_1, `remaining_conic_2] do
    throwError "mathematical printing changed row order or labels: {labels}"
  let source ← printed ``Defined.source false
  unless source.contains "Fn.geoMean" && source.contains "Fn.invProd" &&
      !source.contains "-- Mathematical view" do
    throwError "imported source spelling changed"

namespace Shadow

def Fn.geoMean {n : ℕ} (_ : Fin n → ℝ) : ℝ := 100
def Fn.invProd {n : ℕ} (_ : Fin n → ℝ) : ℝ := 200

variable (n : ℕ) (hn : 0 < n)

run_cmd do
  for (original, copied) in #[(``Defined.source, `sourceReplay),
      (``Defined.lowered, `importedReplay),
      (``Defined.registeredDetailed, `detailedReplay),
      (``specialized, `specializedReplay), (``ready, `readyReplay)] do
    let some view := Syntax.getProblemView? (← getEnv) original
      | throwError "mathematical printing lost imported exact replay"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(noncomputable def $(mkIdent copied) := $term))
    let declaration ← getConstInfo ((← getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      throwError "imported mathematical chain replay is incomplete"

example : sourceReplay n = Defined.source n := rfl
example : importedReplay n hn = Defined.lowered n hn := rfl
example : detailedReplay n hn = Defined.registeredDetailed n hn := rfl
example : specializedReplay = specialized := rfl
example : readyReplay = ready := rfl

end Shadow

example : GlobalEquivalence (Defined.source 3) ready :=
  (Defined.lowered.equivalence 3 (by decide)).trans
    (specialized.equivalence.trans ready.equivalence)
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents
example : ready.conicForm.data.rowCount = 11 := rfl

end
end MorewTest.ImportCompatibility.PowerChainPrinting
