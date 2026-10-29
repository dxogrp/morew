/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ImportCompatibility.PrintDetails.Defined
import MorewTest.Reformulation.PrintDetails

/-!
# Print-time proof detail after importing and continuing a reformulation

The consumer selects proof detail independently of the producer's options.
Continuing the imported target preserves the original finite operands and casts.
-/

namespace MorewTest.ImportCompatibility.PrintDetails

open Lean Lean.Elab.Command Morew
open MorewTest.Reformulation.PrintDetails (printed checkDetails)
noncomputable section

set_option pp.coercions false in
reformulation continued : Defined.lowered := by conic at remaining

run_cmd do
  let required := #["Fin (OfNat.ofNat 3)", "Fin (OfNat.ofNat 4 - OfNat.ofNat 1)",
    "Fin (OfNat.ofNat 2)", "let index", "let offset", "⟨OfNat.ofNat 0", "+ OfNat.ofNat 1",
    "index.val.cast", "minimize t + offset", "coordinate", "shifted", "bound_conic_1"]
  for declaration in #[``Defined.lowered, ``Defined.registeredDetailed, ``continued] do
    checkDetails declaration "firstIndexBound" required
  unless (← printed ``Defined.lowered false) == (← printed ``Defined.registeredDetailed false) do
    throwError "producer proof options changed imported compact printing"
  let output ← printed ``continued false
  unless output.contains "remaining_conic_1" && output.contains "remaining_conic_2" do
    throwError "continued printing lost the newly generated constraints"

-- Consumer-side names cannot capture exact references after either print mode.
namespace Shadow

def firstIndexBound : Nat := 37

run_cmd do
  for (original, copied) in #[(``Defined.lowered, `importedReplay),
      (``Defined.registeredDetailed, `detailedImportedReplay), (``continued, `continuedReplay)] do
    let some view := Syntax.getProblemView? (← getEnv) original
      | throwError "proof-detail printing lost imported exact replay"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(noncomputable def $(mkIdent copied) := $term))
    let declaration ← getConstInfo ((← getCurrNamespace) ++ copied)
    if declaration.type.hasMVar || declaration.type.hasSorry ||
        declaration.value!.hasMVar || declaration.value!.hasSorry then
      throwError "imported proof-detail replay is incomplete"

end Shadow

example : Shadow.importedReplay = Defined.lowered := rfl
example : Shadow.detailedImportedReplay = Defined.registeredDetailed := rfl
example : Shadow.continuedReplay = continued := rfl
example : GlobalEquivalence Defined.source continued :=
  Defined.lowered.equivalence.trans continued.equivalence

end
end MorewTest.ImportCompatibility.PrintDetails
