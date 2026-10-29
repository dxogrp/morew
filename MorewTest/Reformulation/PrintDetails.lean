/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import Lean.Elab.GuardMsgs

/-!
# Proof detail selected when a registered problem is printed

Printing the same declaration under different options must recover its proof
arguments without changing the stored replay views or its mathematical terms.
These ordinary finite coordinates do not depend on power-chain formatting.
-/

namespace MorewTest.Reformulation.PrintDetails

open Lean Lean.Elab.Command Lean.Elab.Tactic.GuardMsgs
open Morew

/-- Capture the actual command, including its selection of print-time options. -/
def printed (declaration : Name) (proofs : Bool) : CommandElabM String := do
  let previous := (← get).messages
  let previousTasks := (← get).snapshotTasks
  modify fun state => { state with snapshotTasks := #[] }
  let messages ← try
    let command ← if proofs then
      `(set_option pp.proofs true in #printp $(mkIdent declaration))
      else `(set_option pp.proofs false in #printp $(mkIdent declaration))
    runAndCollectMessages command
  finally
    modify fun state => { state with messages := previous, snapshotTasks := previousTasks }
  let visible := messages.toList.filter (!·.isSilent)
  let [message] := visible
    | throwError "expected one problem presentation, got {visible.length} diagnostics"
  unless message.severity == .information && !message.isTrace do
    throwError "problem printing produced an unexpected diagnostic: {message.data}"
  return WhitespaceMode.lax.apply (← message.data.toString)

/-- Check both directions of an option change without re-registering the target. -/
def checkDetails (declaration : Name) (proofName : String)
    (required : Array String := #[]) : CommandElabM Unit := do
  let compact ← printed declaration false
  let detailed ← printed declaration true
  let compactAgain ← printed declaration false
  unless compact == compactAgain do
    throwError "detailed printing changed the next compact presentation"
  unless compact.contains "⋯" && !compact.contains proofName do
    throwError "compact printing retained a finite-index proof: {compact}"
  unless detailed.contains proofName && !detailed.contains "⋯" && compact != detailed do
    throwError "print-time pp.proofs did not restore the finite-index proof: {detailed}"
  for fragment in required do
    unless compact.contains fragment && detailed.contains fragment do
      throwError "proof-detail selection changed mathematical syntax {fragment}:\n{compact}\n{detailed}"

noncomputable section

theorem firstIndexBound : 0 < 3 := by decide

def source :=
  problem (x : Fin 3 → ℝ) (t : ℝ)
    let index : Fin (4 - 1) := ⟨0, firstIndexBound⟩
    let offset : ℝ := @Nat.cast ℝ Real.instNatCast index.val
    minimize t + offset
    subject to
      coordinate : x ⟨0, firstIndexBound⟩ ≤ t
      shifted : ∀ j : Fin 2, x ⟨j.val + 1, by omega⟩ ≤ t
      bound : |t| ≤ 3

set_option pp.coercions false in
reformulation target : source := by conic at bound

set_option pp.coercions false in
set_option pp.proofs true in
reformulation registeredDetailed : source := by conic at bound

run_cmd do
  let required := #["Fin (OfNat.ofNat 3)", "Fin (OfNat.ofNat 4 - OfNat.ofNat 1)",
    "Fin (OfNat.ofNat 2)", "let index", "let offset", "⟨OfNat.ofNat 0", "+ OfNat.ofNat 1",
    "index.val.cast", "minimize t + offset", "coordinate", "shifted", "bound_conic_1"]
  checkDetails ``target "firstIndexBound" required
  checkDetails ``registeredDetailed "firstIndexBound" required
  unless (← printed ``target false) == (← printed ``registeredDetailed false) do
    throwError "registration-time pp.proofs changed compact printing"
  -- A source view still retains its user-written spelling when no generated
  -- print presentation has been registered.
  unless (← printed ``source false).contains "firstIndexBound" do
    throwError "generated-proof hiding changed the original source spelling"

run_cmd do
  for (original, exactName, displayName) in
      #[(``target, `exactReplay, `displayReplay),
        (``registeredDetailed, `detailedExactReplay, `detailedDisplayReplay)] do
    let environment ← getEnv
    let some exact := Syntax.getProblemView? environment original
      | throwError "printing lost the exact replay view"
    let some display := Syntax.getProblemDisplayView? environment original
      | throwError "printing lost the ordinary display view"
    -- The ordinary display retains its registration-time policy: the default
    -- view omits the shifted-index proof, while the detailed one can replay.
    let views := if original == ``registeredDetailed then
      #[(exact, exactName), (display, displayName)] else #[(exact, exactName)]
    for (view, name) in views do
      let term ← Lean.Elab.liftMacroM view.toTermSyntax
      elabCommand (← `(noncomputable def $(mkIdent name) := $term))
      let declaration ← getConstInfo ((← getCurrNamespace) ++ name)
      if declaration.type.hasMVar || declaration.type.hasSorry ||
          declaration.value!.hasMVar || declaration.value!.hasSorry then
        throwError "proof-detail printing left an incomplete replay declaration"

example : exactReplay = target := rfl
example : detailedExactReplay = registeredDetailed := rfl
example : detailedDisplayReplay = registeredDetailed := rfl
example : GlobalEquivalence source target := target.equivalence

section AlteredCast

local instance : NatCast ℝ := ⟨fun _ => 7⟩

run_cmd do
  let some view := Syntax.getProblemView? (← getEnv) ``target
    | throwError "missing native-cast replay view"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := mkIdent `nativeCastReplay
  elabCommand (← `(noncomputable def $name := $term))

example : nativeCastReplay = target := rfl

end AlteredCast

end
end MorewTest.Reformulation.PrintDetails
