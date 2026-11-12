/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax.Presentation
import Lean.Elab.Command

/-! Shared checks for complete declarations reconstructed from stored problem views. -/

namespace MorewTest.Reformulation

open Lean Lean.Elab.Command

/-- Rebuild a selected view in the caller's namespace and elaboration context. -/
def replayView (view : Morew.Syntax.ProblemView) (name : Name)
    (incompleteMessage : String) : CommandElabM Unit := do
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  elabCommand (← `(noncomputable def $(mkIdent name) := $term))
  let declaration ← getConstInfo ((← getCurrNamespace) ++ name)
  if declaration.type.hasMVar || declaration.type.hasSorry ||
      declaration.value!.hasMVar || declaration.value!.hasSorry then
    throwError "{incompleteMessage}"

end MorewTest.Reformulation
