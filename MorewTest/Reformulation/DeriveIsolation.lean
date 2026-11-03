/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Incomplete derived-constraint expressions

The command elaborates each step through `runTermElabM`, which starts a fresh
metavariable context rather than accepting caller metavariables. These tests
exercise unresolved expressions inside that boundary and check that rejecting
them also rolls back the command's declarations and presentation metadata.
-/

namespace MorewTest.Reformulation.DeriveIsolation

open Lean Lean.Meta Lean.Elab.Term
open Morew

noncomputable section

-- These elaborators bypass ordinary placeholder diagnostics, so the derive
-- handler itself must refuse the resulting incomplete expression.
elab "derive_missing%" : term <= expected => do
  mkFreshExprMVar expected

elab "derive_synthetic_sorry%" : term <= expected => do
  mkSorry expected true

elab "derive_user_sorry%" : term <= expected => do
  mkSorry expected false

-- An already solved metavariable is complete evidence, and should be accepted.
elab "derive_completed%" : term <= expected => do
  let proof ← elabTermEnsuringType (← `(by intro _ _; trivial)) expected
  synthesizeSyntheticMVarsNoPostponing
  let hole ← mkFreshExprMVar expected
  hole.mvarId!.assign (← instantiateMVars proof)
  pure hole

elab "assert_derive_isolated% " target:ident " in " nested:command : command => do
  let before ← getEnv
  let target := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    throwError "rejected incomplete derivation changed declarations"
  for name in #[target, target ++ `equivalence] do
    if after.contains name || (Morew.Syntax.getProblemView? after name).isSome then
      throwError "rejected incomplete derivation retained an output or its metadata"

def source := problem (x : ℝ) minimize x

theorem trueProof : ∀ point, source.feasible point → True := fun _ _ => True.intro

#guard_error_fragments ["derived constraint", "placeholders"] in
assert_derive_isolated% userPredicate in
reformulation userPredicate : source := by
  derive missing : derive_user_sorry% using trueProof

#guard_error_fragments ["derived constraint", "placeholders"] in
assert_derive_isolated% syntheticPredicate in
reformulation syntheticPredicate : source := by
  derive missing : derive_synthetic_sorry% using trueProof

-- An incomplete predicate is rejected before the supplied proof could infer it.
#guard_error_fragments ["derived constraint", "unresolved metavariables"] in
assert_derive_isolated% missingPredicate in
reformulation missingPredicate : source := by
  derive missing : derive_missing% using trueProof

#guard_error_fragments ["derived constraint proof", "placeholders"] in
assert_derive_isolated% userProof in
reformulation userProof : source := by
  derive self : x = x using derive_user_sorry%

#guard_error_fragments ["derived constraint proof", "placeholders"] in
assert_derive_isolated% syntheticProof in
reformulation syntheticProof : source := by
  derive self : x = x using derive_synthetic_sorry%

#guard_error_fragments ["derived constraint proof", "unresolved metavariables"] in
assert_derive_isolated% missingProof in
reformulation missingProof : source := by
  derive self : x = x using derive_missing%

-- A later placeholder must also discard a helper from an earlier valid step.
#guard_error_fragments ["derived constraint proof", "placeholders"] in
assert_derive_isolated% latePlaceholder in
reformulation latePlaceholder : source := by
  derive first : True using derive_completed%
  derive second : x = x using derive_synthetic_sorry%

-- Reuse a rejected name to check recovery, and retain an explicit True row.
reformulation latePlaceholder : source := by
  derive first : True using derive_completed%

example : GlobalEquivalence source latePlaceholder := latePlaceholder.equivalence
example (x : ℝ) : latePlaceholder.feasible x ↔ True := Iff.rfl

end
end MorewTest.Reformulation.DeriveIsolation
