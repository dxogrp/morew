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

end MorewTest.Diagnostics
