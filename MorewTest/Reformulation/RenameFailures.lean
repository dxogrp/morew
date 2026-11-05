/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.DiagnosticsSupport
import MorewTest.Environment

/-!
# Constraint-renaming failures and rollback

Source resolution precedes destination preflight. Failed commands retain no
declarations or presentation metadata, including helpers from earlier steps.
-/

namespace MorewTest.Reformulation.RenameFailures

open Morew
noncomputable section

-- `rename` and `to` are reserved; `constraint` remains an ordinary identifier.
def keywordBinders (constraint «rename» «to» : Nat) : Nat :=
  constraint + «rename» + «to»

example : keywordBinders 1 2 3 = 6 := rfl

elab "assert_rename_atomic% " target:ident aliasName:ident " in " nested:command :
    command => do
  let before ← Lean.getEnv
  let namespaceName ← Lean.getCurrNamespace
  let target := namespaceName ++ target.getId
  let aliasName := namespaceName ++ aliasName.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed renaming changed declarations or certificate helpers"
  for name in #[target, target ++ `equiv, aliasName,
      target ++ `conicForm, target ++ `isConic,
      target ++ `nlpForm, target ++ `isSmoothNLP] do
    if after.contains name then Lean.throwError m!"failed renaming emitted {name}"
    if (Morew.Syntax.getProblemView? after name).isSome ||
        (Morew.Syntax.getProblemDisplayView? after name).isSome ||
        (Morew.Syntax.getProblemPrintPresentation? after name).isSome then
      Lean.throwError m!"failed renaming registered presentation metadata for {name}"

def bounded :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : -1 ≤ x
      cap : |x| ≤ 3
      upper : x ≤ 1

def empty := problem (x : ℝ) minimize x

-- An occupied destination cannot hide the missing-source diagnostic.
#guard_error_fragments ["unknown or stale constraint label `missing`"] in
assert_rename_atomic% missingSource missingSourceAlias in
reformulation missingSource : bounded certificate missingSourceAlias := by
  rename missing to upper

#guard_error_fragments ["unknown or stale constraint label `missing`"] in
assert_rename_atomic% missingNoOp missingNoOpAlias in
reformulation missingNoOp : bounded certificate missingNoOpAlias := by
  rename missing to missing

#guard_error_fragments ["unknown or stale constraint label `missing`"] in
assert_rename_atomic% emptySource emptySourceAlias in
reformulation emptySource : empty certificate emptySourceAlias := by
  rename missing to fresh

#guard_error_fragments ["constraint name `upper` already exists"] in
assert_rename_atomic% occupied occupiedAlias in
reformulation occupied : bounded certificate occupiedAlias := by
  rename lower to upper

#guard_error_fragments ["unknown or stale constraint label `cap`"] in
assert_rename_atomic% staleOccurrence staleOccurrenceAlias in
reformulation staleOccurrence : bounded certificate staleOccurrenceAlias := by
  rename cap to bound
  epigraph t at (|x|) in cap

#guard_error_fragments ["unknown or stale constraint label `lower`"] in
assert_rename_atomic% staleRename staleRenameAlias in
reformulation staleRename : bounded certificate staleRenameAlias := by
  rename lower to fresh
  rename lower to newer

-- Ordinary namespace components participate in exact label lookup.
def qualified :=
  problem (x : ℝ)
    minimize x
    subject to
      labels.cap : x ≤ 3
      labels.other : 0 ≤ x

#guard_error_fragments ["unknown or stale constraint label `cap`"] in
assert_rename_atomic% unqualified unqualifiedAlias in
reformulation unqualified : qualified certificate unqualifiedAlias := by
  rename cap to fresh

#guard_error_fragments ["constraint name `labels.other` already exists"] in
assert_rename_atomic% qualifiedCollision qualifiedCollisionAlias in
reformulation qualifiedCollision : qualified certificate qualifiedCollisionAlias := by
  rename labels.cap to labels.other

def affine :=
  problem (x : ℝ)
    minimize x
    subject to
      cap : x ≤ 3

-- Ordinary and escaped identifiers can be used as labels and renamed back
-- to their original spelling.
reformulation contextualRoundTrip : affine := by
  rename cap to «to»
  rename «to» to constraint
  rename constraint to «rename»
  rename «rename» to cap

example : contextualRoundTrip = affine := rfl
example : GlobalEquiv affine contextualRoundTrip := contextualRoundTrip.equiv

run_cmd do
  let some view := Morew.Syntax.getProblemDisplayView? (← Lean.getEnv) ``contextualRoundTrip
    | Lean.throwError "contextual label round trip lost its display metadata"
  unless view.constraints.map (·.name.eraseMacroScopes) == #[`cap] do
    Lean.throwError "contextual label round trip retained an intermediate label"

run_cmd do
  for malformed in #[
      "rename lower to", "rename to upper",
      "rename constraint lower to upper", "rename lower upper"] do
    let command := "reformulation malformed : bounded := by\n  " ++ malformed
    match Lean.Parser.runParserCategory (← Lean.getEnv) `command command with
    | .error _ => pure ()
    | .ok _ => Lean.throwError "malformed renaming syntax was accepted: {malformed}"

end

end MorewTest.Reformulation.RenameFailures
