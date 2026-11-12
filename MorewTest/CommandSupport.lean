/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Elab.Command
import MorewTest.Environment

/-! Shared command elaboration and declaration rollback checks. -/

namespace MorewTest

open Lean Lean.Elab.Command

/-- Elaborate a command and reject added local declarations, retaining diagnostics and
environment changes for surrounding assertions. Declaration removal is allowed. -/
def elabNoNewDeclarations (command : Syntax) (failureMessage : Name → MessageData) :
    CommandElabM Unit := do
  let before ← getEnv
  try elabCommand command catch error => Lean.Elab.logException error
  if let some name := newLocalDeclaration? before (← getEnv) then
    throwError (failureMessage name)

end MorewTest
