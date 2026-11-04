/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.PrintSupport

/-! Shared checks for Euclidean presentation reconstruction. -/

namespace MorewTest.Reformulation.EuclideanPrintingSupport

open Lean Lean.Elab.Command Morew

/-- The readable coordinate shorthand belongs only to the printed representations. -/
def checkStoredProjections (declaration : Name) : CommandElabM Unit := do
  for getter in #[Syntax.getProblemView?, Syntax.getProblemDisplayView?] do
    let some view := getter (← getEnv) declaration
      | throwError "Euclidean printing lost a stored reconstruction view"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let output := (← liftCoreM <| PrettyPrinter.ppTerm ⟨term⟩).pretty
    unless output.contains "ofLp" do
      throwError "print-only Euclidean coordinates entered reconstruction syntax: {output}"

/-- Rebuild both stored views in the caller's instance context. -/
def replayStored (declaration exactName displayName : Name) : CommandElabM Unit := do
  for (getter, name) in #[(Syntax.getProblemView?, exactName),
      (Syntax.getProblemDisplayView?, displayName)] do
    let some view := getter (← getEnv) declaration
      | throwError "missing Euclidean reconstruction view"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    elabCommand (← `(noncomputable def $(mkIdent name) := $term))
    let result ← getConstInfo ((← getCurrNamespace) ++ name)
    if result.type.hasMVar || result.type.hasSorry ||
        result.value!.hasMVar || result.value!.hasSorry then
      throwError "Euclidean replay contains incomplete evidence"

end MorewTest.Reformulation.EuclideanPrintingSupport
