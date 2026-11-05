/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.DiagnosticsSupport
import MorewTest.Environment

/-!
# Targeted polyhedral diagnostics and rollback

Rejected rules must name the selected row and leave no target, certificate,
alias, or registered presentation behind, including after an earlier success.
-/

namespace MorewTest.Reformulation.PolyhedralFailures

open Morew

noncomputable section

private def assertAbsent (target aliasName : Lean.Name) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  for name in #[target, target ++ `equiv, aliasName] do
    if env.contains name then
      Lean.throwError "failed conic rewrite emitted declaration `{name}`"
  if (Morew.Syntax.getProblemView? env target).isSome then
    Lean.throwError "failed conic rewrite registered presentation metadata"

elab "assert_polyhedral_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let `(command| reformulation $target:ident : $_source:ident
      $[certificate $aliasName:ident]? := by $_steps:reformulationStep*) := nested
    | Lean.throwError "expected a reformulation command"
  let namespaceName ← Lean.getCurrNamespace
  let targetName := namespaceName ++ target.getId
  let names := #[targetName, targetName ++ `equiv] ++
    (match aliasName with
      | some aliasName => #[namespaceName ++ aliasName.getId]
      | none => #[])
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed conic label lookup changed local declarations"
  for name in names do
    if after.contains name then
      Lean.throwError "failed conic label lookup emitted {name}"
    if (Morew.Syntax.getProblemView? after name).isSome ||
        (Morew.Syntax.getProblemDisplayView? after name).isSome ||
        (Morew.Syntax.getProblemPrintPresentation? after name).isSome then
      Lean.throwError "failed conic label lookup registered presentation metadata for {name}"

def source :=
  problem (x : ℝ)
    minimize x
    subject to
      bound : |x| ≤ 3

/-- error: unknown or stale constraint label `missing` -/
#guard_msgs in
assert_polyhedral_atomic%
reformulation unknown : source certificate unknownAlias := by
  conic at missing

/-- error: unknown or stale constraint label `bound` -/
#guard_msgs in
reformulation stale : source certificate staleAlias := by
  conic at bound
  conic at bound

def reverseSource :=
  problem (x : ℝ)
    minimize x
    subject to
      reversed : 1 ≤ |x|

/-- error: constraint `reversed`: no supported registered conic rule matches the entire selected predicate and bound polarity -/
#guard_msgs (substring := true) in
reformulation reverse : reverseSource certificate reverseAlias := by
  conic at reversed

def nonlinearSource :=
  problem (x : ℝ)
    minimize x
    subject to
      nonlinear : |x ^ 2| ≤ 3

#guard_error_fragments ["constraint `nonlinear`: no registered exact conic rule was fully certified:",
  "Morew.Rewrite.absEpigraph: generated row"] in
reformulation nonlinear : nonlinearSource certificate nonlinearAlias := by
  conic at nonlinear

/-- error: constraint `bound`: expected ExactConstraintLift -/
#guard_msgs (substring := true) in
reformulation wrongRecord : source certificate wrongRecordAlias := by
  conic at bound using (0 : ℝ)

/-- An explicit proof parameter remains an obligation even when the selected
predicate also matches the ordinary automatic absolute-value rule. -/
def guardedLift (_ : True) : ExactConstraintLift (fun x : ℝ => |x| ≤ 3) :=
  ExactConstraintLift.ofIff (fun x => x ≤ 3 ∧ -x ≤ 3)
    (fun x => Morew.Rewrite.Polyhedral.abs_le_iff x 3)

/-- error: constraint `bound`: failed to elaborate exact rule: exact rule contains unresolved metavariables -/
#guard_msgs in
reformulation unresolvedRule : source certificate unresolvedRuleAlias := by
  conic at bound using (guardedLift _)

def twoBounds :=
  problem (x : ℝ)
    minimize x
    subject to
      before : |x| ≤ 4
      bound : |x| ≤ 3

/-- error: constraint `bound`: failed to elaborate exact rule: exact rule contains unresolved metavariables -/
#guard_msgs in
reformulation unresolvedAfterSuccess : twoBounds certificate unresolvedAfterSuccessAlias := by
  conic at before
  conic at bound using (guardedLift _)

def wrongLift : ExactConstraintLift (fun x : ℝ => x ≤ 3) :=
  ExactConstraintLift.ofIff (fun x => x ≤ 3) (fun _ => Iff.rfl)

#guard_error_fragments ["constraint `bound`: representation operation", "does not match"] in
reformulation wrongPredicate : source certificate wrongPredicateAlias := by
  conic at bound using wrongLift

def preservedNonlinear : ExactConstraintLift (fun x : ℝ => |x ^ 2| ≤ 3) :=
  ExactConstraintLift.ofIff (fun x => |x ^ 2| ≤ 3) (fun _ => Iff.rfl)

/-- error: constraint `nonlinear`: generated row -/
#guard_msgs (substring := true) in
reformulation customNonlinear : nonlinearSource certificate customNonlinearAlias := by
  conic at nonlinear using preservedNonlinear

def strictSource :=
  problem (x : ℝ)
    minimize x
    subject to
      strict : x < 3

def strictLift : ExactConstraintLift (fun x : ℝ => x < 3) :=
  ExactConstraintLift.ofIff (fun x => x < 3) (fun _ => Iff.rfl)

/-- error: constraint `strict`: unsupported exact target predicate -/
#guard_msgs (substring := true) in
reformulation strict : strictSource certificate strictAlias := by
  conic at strict using strictLift

def booleanLift : ExactConstraintLift (fun x : ℝ => |x| ≤ 3) where
  Auxiliary := Bool
  target x _ := x ≤ 3 ∧ -x ≤ 3
  source_iff_exists x := by
    simp [Morew.Rewrite.Polyhedral.abs_le_iff]

/-- error: constraint `bound`: unsupported exact-lift decision space -/
#guard_msgs (substring := true) in
reformulation booleanAuxiliary : source certificate booleanAuxiliaryAlias := by
  conic at bound using booleanLift

run_cmd do
  let parentNamespace := `MorewTest.Reformulation.PolyhedralFailures
  for target in #[`unknown, `stale, `reverse, `nonlinear, `wrongRecord,
      `unresolvedRule, `unresolvedAfterSuccess, `wrongPredicate,
      `customNonlinear, `strict, `booleanAuxiliary] do
    assertAbsent (parentNamespace ++ target)
      (parentNamespace ++ Lean.Name.mkSimple (target.toString ++ "Alias"))

reformulation validAfterFailures : source := by
  conic at bound
  epigraph t

example : GlobalEquiv source validAfterFailures := validAfterFailures.equiv

end

end MorewTest.Reformulation.PolyhedralFailures
