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

namespace BinderTypes

reformulation continued : Defined.BinderTypes.lowered := by conic at remaining

run_cmd do
  for declaration in #[``Defined.BinderTypes.lowered, ``Defined.BinderTypes.registeredDetailed] do
    checkDetails declaration "Nat.zero_lt_two" #["Indexed ⟨0,", "entry", "x : ℝ"]
  let details ← printed ``continued true
  let proofName := if details.contains "Nat.zero_lt_two" then "Nat.zero_lt_two" else "_proof_"
  checkDetails ``continued proofName #["Indexed ⟨0,", "entry", "x : ℝ"]
  for declaration in #[``Defined.BinderTypes.lowered,
      ``Defined.BinderTypes.registeredDetailed, ``continued] do
    for getter in #[Syntax.getProblemView?, Syntax.getProblemDisplayView?] do
      let some view := getter (← getEnv) declaration
        | throwError "imported binder proof printing lost a stored view"
      let binderType := (← liftCoreM <| PrettyPrinter.ppTerm ⟨view.binders[0]!.typeSyntax⟩).pretty
      unless !binderType.contains "⋯" &&
          (binderType.contains "Nat.zero_lt_two" || binderType.contains "_proof_") do
        throwError "compact printing changed an imported reconstruction type: {binderType}"
  unless (← printed ``Defined.BinderTypes.lowered false) ==
      (← printed ``Defined.BinderTypes.registeredDetailed false) do
    throwError "producer proof options changed compact imported binder types"
  for (getter, name) in #[(Syntax.getProblemView?, `exactReplay),
      (Syntax.getProblemDisplayView?, `displayReplay)] do
    let some view := getter (← getEnv) ``continued
      | throwError "missing continued binder presentation"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(noncomputable def $(mkIdent name) := $term))

example : exactReplay = continued := rfl
example : displayReplay = continued := rfl
example : GlobalEquivalence (Defined.BinderTypes.source 0) continued :=
  Defined.BinderTypes.lowered.equivalence.trans continued.equivalence

end BinderTypes

end
end MorewTest.ImportCompatibility.PrintDetails
