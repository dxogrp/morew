/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax.Printer
import Lean.Elab.GuardMsgs

/-!
# Shared problem-printing assertions

Reusable assertions independent of the reformulation test suites.
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

end MorewTest.Reformulation.PrintDetails

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

end MorewTest.Reformulation.PowerChainPrinting
