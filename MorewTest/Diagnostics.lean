/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.DiagnosticsSupport

namespace MorewTest.Diagnostics

open Lean Elab Command Tactic.GuardMsgs

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
