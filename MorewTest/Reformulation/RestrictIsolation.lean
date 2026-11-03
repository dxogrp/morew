/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Incomplete restriction conditions and repair certificates

Each step elaborates in a fresh `runTermElabM` metavariable context. These
elaborators bypass ordinary placeholder errors to exercise the handler's own
completeness checks and the enclosing command's declaration/metadata rollback.
-/

namespace MorewTest.Reformulation.RestrictIsolation

open Lean Lean.Meta Lean.Elab.Term
open Morew
noncomputable section

elab "restrict_missing%" : term <= expected => do
  mkFreshExprMVar expected

elab "restrict_synthetic_sorry%" : term <= expected => do
  mkSorry expected true

elab "restrict_user_sorry%" : term <= expected => do
  mkSorry expected false

elab "restrict_completed%" : term <= expected => do
  let proof ← elabTermEnsuringType (← `({
    map := fun point => ⟨point.1, point.2, True.intro⟩
    objective_le := fun _ => le_rfl })) expected
  synthesizeSyntheticMVarsNoPostponing
  let hole ← mkFreshExprMVar expected
  hole.mvarId!.assign (← instantiateMVars proof)
  pure hole

elab "assert_restrict_isolated% " target:ident " in " nested:command : command => do
  let before ← getEnv
  let target := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    throwError "rejected incomplete restriction changed declarations"
  for name in #[target, target ++ `equivalence] do
    if after.contains name || (Morew.Syntax.getProblemView? after name).isSome then
      throwError "rejected incomplete restriction retained an output or its metadata"

def source := problem (x : ℝ) minimize x

def trueRepair : GlobalImprovement source (source.addConstraint (fun _ => True)) where
  map point := ⟨point.1, point.2, True.intro⟩
  objective_le _ := le_rfl

#guard_error_fragments ["restriction", "placeholders"] in
assert_restrict_isolated% userPredicate in
reformulation userPredicate : source := by
  restrict missing : restrict_user_sorry% using trueRepair

#guard_error_fragments ["restriction", "placeholders"] in
assert_restrict_isolated% syntheticPredicate in
reformulation syntheticPredicate : source := by
  restrict missing : restrict_synthetic_sorry% using trueRepair

-- The certificate cannot assign a missing condition after its elaboration.
#guard_error_fragments ["restriction", "unresolved metavariables"] in
assert_restrict_isolated% missingPredicate in
reformulation missingPredicate : source := by
  restrict missing : restrict_missing% using trueRepair

#guard_error_fragments ["restriction certificate", "placeholders"] in
assert_restrict_isolated% userCertificate in
reformulation userCertificate : source := by
  restrict self : True using restrict_user_sorry%

#guard_error_fragments ["restriction certificate", "placeholders"] in
assert_restrict_isolated% syntheticCertificate in
reformulation syntheticCertificate : source := by
  restrict self : True using restrict_synthetic_sorry%

#guard_error_fragments ["restriction certificate", "unresolved metavariables"] in
assert_restrict_isolated% missingCertificate in
reformulation missingCertificate : source := by
  restrict self : True using restrict_missing%

#guard_error_fragments ["restriction certificate", "placeholders"] in
assert_restrict_isolated% incompleteField in
reformulation incompleteField : source := by
  restrict self : True using {
    map := fun point => ⟨point.1, point.2, True.intro⟩
    objective_le := restrict_synthetic_sorry% }

-- A later error must discard the helper and metadata of an earlier valid step.
#guard_error_fragments ["restriction certificate", "placeholders"] in
assert_restrict_isolated% latePlaceholder in
reformulation latePlaceholder : source := by
  restrict first : True using restrict_completed%
  restrict second : True using restrict_synthetic_sorry%

reformulation latePlaceholder : source := by
  restrict first : True using restrict_completed%

example : GlobalEquivalence source latePlaceholder := latePlaceholder.equivalence
example (x : ℝ) : latePlaceholder.feasible x ↔ True := Iff.rfl

end
end MorewTest.Reformulation.RestrictIsolation
