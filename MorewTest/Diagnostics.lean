/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Elab.GuardMsgs

/-!
# Diagnostic fragment assertions

`#guard_error_fragments ["label", "reason"] in command` requires exactly one
visible error containing every fragment, ignoring whitespace differences. It
does not match across separate diagnostics or accept extra warnings or messages.
Use it when intervening diagnostic details are outside a test's purpose; keep
`#guard_msgs` for exact presentation and diagnostic-order expectations.

The command preserves environment changes so it cannot hide a failed rollback
assertion. Only the captured messages are consumed.
-/

namespace MorewTest.Diagnostics

open Lean Elab Command Tactic.GuardMsgs

elab "#guard_error_fragments " "[" fragments:str,+ "]" " in " cmd:command : command => do
  let fragments := fragments.getElems.map (WhitespaceMode.lax.apply ·.getString)
  if fragments.any String.isEmpty then
    throwError "diagnostic fragments must be nonempty"
  let previous := (← get).messages
  let previousTasks := (← get).snapshotTasks
  modify fun state => { state with snapshotTasks := #[] }
  let messages ← try
    runAndCollectMessages cmd
  finally
    modify fun state => { state with messages := previous, snapshotTasks := previousTasks }
  let visible := messages.toList.filter (!·.isSilent)
  let [message] := visible
    | throwError "expected exactly one error, got {visible.length} diagnostics:\n{MessageData.joinSep (visible.map (·.data)) "\n"}"
  unless message.severity == .error && !message.isTrace do
    throwError "expected an error, got a non-error diagnostic:\n{message.data}"
  let text := WhitespaceMode.lax.apply (← message.data.toString)
  for fragment in fragments do
    unless text.contains fragment do
      throwError "expected error to contain {fragment}:\n{message.data}"

/-! The guard must reject false positives while preserving observable effects. -/

#guard_error_fragments ["constraint `row`:", "rule: missing margin"] in
run_cmd logError "constraint `row`:\nunrelated candidate details\nrule: missing   margin"

#guard_error_fragments ["thrown error"] in
run_cmd (throwError "a thrown error" : CommandElabM Unit)

/--
error: expected error to contain missing:
present
-/
#guard_msgs in
#guard_error_fragments ["present", "missing"] in
run_cmd logError "present"

/-- error: expected exactly one error, got 0 diagnostics: -/
#guard_msgs in
#guard_error_fragments ["missing"] in
run_cmd pure ()

set_option warningAsError false in
/--
error: expected an error, got a non-error diagnostic:
warning only
-/
#guard_msgs in
#guard_error_fragments ["warning only"] in
run_cmd logWarning "warning only"

/--
error: expected exactly one error, got 2 diagnostics:
label
reason
-/
#guard_msgs in
#guard_error_fragments ["label", "reason"] in
run_cmd do
  logError "label"
  logError "reason"

/--
error: expected exactly one error, got 2 diagnostics:
expected
rollback failed
-/
#guard_msgs in
#guard_error_fragments ["expected"] in
run_cmd do
  logError "expected"
  logError "rollback failed"

/--
error: expected exactly one error, got 2 diagnostics:
expected
extra warning
-/
#guard_msgs in
#guard_error_fragments ["expected"] in
run_cmd do
  logError "expected"
  logWarning "extra warning"

/--
error: expected exactly one error, got 2 diagnostics:
expected
extra information
-/
#guard_msgs in
#guard_error_fragments ["expected"] in
run_cmd do
  logError "expected"
  logInfo "extra information"

/-- error: diagnostic fragments must be nonempty -/
#guard_msgs in
#guard_error_fragments [" "] in
run_cmd logError "unused"

set_option warningAsError false in
/-- warning: earlier warning -/
#guard_msgs in
run_cmd do
  logWarning "earlier warning"
  elabCommand (← `(#guard_error_fragments ["expected"] in run_cmd logError "expected"))

#guard_error_fragments ["expected"] in
run_cmd do
  let name := mkIdent `diagnosticSentinel
  elabCommand (← `(def $name : Nat := 7))
  logError "expected"

example : diagnosticSentinel = 7 := rfl

end MorewTest.Diagnostics
