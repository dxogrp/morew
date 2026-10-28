/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Elab.Command
import Lean.Elab.BuiltinCommand
import Lean.AddDecl
import MorewTest.Environment

/-!
# Regression tests for local declaration rollback checks

Use kernel-checked auxiliary theorems to distinguish correct rollback, leaks,
rollback past the original snapshot, and replacement by a different name.
Fixture declarations are removed even if an assertion fails.
-/

namespace MorewTest.EnvironmentRollback

open Lean Elab Command

private def addAuxiliary (name : Name) : CoreM Unit :=
  addDecl <| .thmDecl {
    name
    levelParams := []
    type := mkConst ``True
    value := mkConst ``True.intro
  }

run_cmd liftCoreM do
  let original ← getEnv
  try
    unless (newLocalDeclaration? original original).isNone &&
        sameLocalDeclarationNames original original do
      throwError "unchanged environment was rejected"

    let first := `MorewTest.EnvironmentRollback._firstAuxiliary
    let withFirst ← withoutModifyingEnv do
      addAuxiliary first
      let result ← getEnv
      unless newLocalDeclaration? original result == some first do
        throwError "checked auxiliary leak was not identified by name"
      if sameLocalDeclarationNames original result then
        throwError "an added auxiliary passed the equality check"
      return result
    let restored ← getEnv
    unless (newLocalDeclaration? original restored).isNone &&
        sameLocalDeclarationNames original restored do
      throwError "proper auxiliary rollback was rejected"

    -- The one-way leak check deliberately permits removals; equality must not.
    unless (newLocalDeclaration? withFirst restored).isNone do
      throwError "one-way leak check rejected a declaration removal"
    if sameLocalDeclarationNames withFirst restored then
      throwError "rollback past the baseline declaration was accepted"

    let second := `MorewTest.EnvironmentRollback._secondAuxiliary
    addAuxiliary second
    let withSecond ← getEnv
    let count := fun (environment : Environment) =>
      environment.constants.map₂.foldl (fun count _ _ => count + 1) (0 : Nat)
    unless count withFirst == count withSecond do
      throwError "replacement regression must have equal declaration counts"
    unless newLocalDeclaration? withFirst withSecond == some second &&
        newLocalDeclaration? withSecond withFirst == some first do
      throwError "equal-count replacement was not identified in both directions"
    if sameLocalDeclarationNames withFirst withSecond then
      throwError "equal-count replacement passed the equality check"
  finally
    setEnv original

end MorewTest.EnvironmentRollback
