/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Command
import MorewTest.Environment

/-!
# Occurrence-bound selection failures and atomicity

Bad selections, unsupported polarities, and invalid explicit evidence leave no
declarations or presentation metadata, including after an earlier valid step.
-/

namespace MorewTest.Reformulation.OccurrenceFailures

open Morew
noncomputable section

private def assertAbsent (target aliasName : Lean.Name) :
    Lean.Elab.Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  for name in #[target, target ++ `equivalence, aliasName] do
    if env.contains name then
      Lean.throwError "failed occurrence lift emitted declaration `{name}`"
  if (Morew.Syntax.getProblemView? env target).isSome then
    Lean.throwError "failed occurrence lift registered presentation metadata"

elab "assert_occurrence_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  if let some name := MorewTest.newLocalDeclaration? before after then
    Lean.throwError m!"failed occurrence lift leaked declaration {name}"

def source :=
  problem (x : ℝ)
    let loss := x ^ 2
    let penalty := |x|
    minimize loss + penalty
    subject to
      cap : loss ≤ 10
      lower : 1 ≤ loss

/-- error: unknown model-local definition `missing` -/
#guard_msgs in
reformulation unknown : source certificate unknownAlias := by
  epigraph t at missing

/-- error: unknown model-local definition `x` -/
#guard_msgs in
reformulation decisionName : source certificate decisionNameAlias := by
  epigraph t at x

/-- error: unknown model-local definition `cap` -/
#guard_msgs in
reformulation constraintName : source certificate constraintNameAlias := by
  epigraph t at cap

/-- error: unknown or stale constraint label `missing` -/
#guard_msgs in
reformulation unknownRow : source certificate unknownRowAlias := by
  epigraph t at loss in missing

/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation noExpression : source certificate noExpressionAlias := by
  epigraph t at (x ^ 2)

/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation wrongLocation : source certificate wrongLocationAlias := by
  epigraph t at penalty in cap

def indirectSource :=
  problem (x : ℝ)
    let loss := x ^ 2
    let total := loss + |x|
    minimize total

/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation indirect : indirectSource certificate indirectAlias := by
  epigraph t at loss

def repeatedSource :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize loss + loss

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeated : repeatedSource certificate repeatedAlias := by
  epigraph t at loss

def repeatedExpressionSource := problem (x : ℝ) minimize x ^ 2 + x ^ 2

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedExpression : repeatedExpressionSource certificate repeatedExpressionAlias := by
  epigraph t at (x ^ 2)

/-- error: the occurrence bound has the wrong objective sense -/
#guard_msgs in
reformulation wrongSense : source certificate wrongSenseAlias := by
  hypograph t at loss

/-- error: cannot certify bound context -/
#guard_msgs (substring := true) in
reformulation wrongPolarity : source certificate wrongPolarityAlias := by
  epigraph t at loss in lower

def equalitySource := problem (x : ℝ) minimize x subject to equal : x ^ 2 = 1

/-- error: cannot certify bound context -/
#guard_msgs (substring := true) in
reformulation equality : equalitySource certificate equalityAlias := by
  epigraph t at (x ^ 2) in equal

def nonmonotoneSource := problem (x : ℝ) minimize |x ^ 2|

/-- error: cannot certify bound context -/
#guard_msgs (substring := true) in
reformulation nonmonotone : nonmonotoneSource certificate nonmonotoneAlias := by
  epigraph t at (x ^ 2)

/-- error: decision variable `x` already exists -/
#guard_msgs in
reformulation binderCollision : source certificate binderCollisionAlias := by
  epigraph x at loss

/-- error: decision variable `loss` conflicts with a model-local definition -/
#guard_msgs (substring := true) in
reformulation definitionCollision : source certificate definitionCollisionAlias := by
  epigraph loss at penalty

/-- error: constraint name `cap` already exists -/
#guard_msgs in
reformulation labelCollision : source certificate labelCollisionAlias := by
  epigraph t at loss as cap

def occupiedDefault :=
  problem (x : ℝ)
    minimize x ^ 2 + x
    subject to
      epigraph_t : 0 ≤ x

/-- error: generated constraint name `epigraph_t` already exists; use `as <label>` to choose a different constraint label -/
#guard_msgs in
reformulation defaultLabelCollision : occupiedDefault certificate defaultLabelCollisionAlias := by
  epigraph t at (x ^ 2)

structure Unordered where
  value : ℝ

def unordered := problem (x : Unordered) minimize x.value

/-- error: failed to synthesize -/
#guard_msgs (substring := true) in
reformulation missingOrder : unordered certificate missingOrderAlias := by
  epigraph t at (x)

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
reformulation invalidEvidence : source certificate invalidEvidenceAlias := by
  epigraph t at loss using (0 : ℝ)

theorem wrongSelectionContext : ObjectiveEpigraphContext source
    (fun x => |x|) (fun x t => x ^ 2 + t) where
  atValue _ := rfl
  backward _ _ _ bound := add_le_add le_rfl bound

/-- error: Type mismatch -/
#guard_msgs (substring := true) in
reformulation mismatchedEvidence : source certificate mismatchedEvidenceAlias := by
  epigraph t at loss using wrongSelectionContext

/-- error: constraint name `shared` already exists -/
#guard_msgs in
assert_occurrence_atomic%
reformulation lateFailure : source certificate lateFailureAlias := by
  epigraph t at loss as shared
  epigraph s at penalty as shared

def dependentSource :=
  problem (n : ℕ)
    minimize ((⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) : ℕ)

/-- error: the selected type depends on a decision variable; dependent auxiliaries are unsupported -/
#guard_msgs in
reformulation dependent : dependentSource certificate dependentAlias := by
  epigraph t at ((⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)))

def terminalSource := problem (x : ℝ) minimize x

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs (substring := true) in
reformulation afterTerminal : terminalSource certificate afterTerminalAlias := by
  conic
  epigraph t at (x)

run_cmd do
  for suffix in #["unknown", "decisionName", "constraintName", "unknownRow",
      "noExpression", "wrongLocation", "indirect", "repeated", "repeatedExpression",
      "wrongSense", "wrongPolarity", "equality", "nonmonotone", "binderCollision",
      "definitionCollision", "labelCollision", "invalidEvidence", "lateFailure",
      "mismatchedEvidence", "defaultLabelCollision", "missingOrder", "dependent", "afterTerminal"] do
    let ns := `MorewTest.Reformulation.OccurrenceFailures
    assertAbsent (ns ++ Lean.Name.mkSimple suffix) (ns ++ Lean.Name.mkSimple (suffix ++ "Alias"))

run_cmd do
  for step in #["epigraph t at", "epigraph t at loss in", "epigraph t at loss as",
      "epigraph t at loss as cap in lower", "epigraph t at loss in cap in lower",
      "hypograph t at loss as a as b", "epigraph t at loss using"] do
    let command := "reformulation malformed : source := by\n  " ++ step
    match Lean.Parser.runParserCategory (← Lean.getEnv) `command command with
    | .error _ => pure ()
    | .ok _ => Lean.throwError "accepted malformed occurrence step: {step}"

-- Reusing the failed target name also verifies that rollback permits recovery.
reformulation lateFailure : source certificate lateFailureAlias := by
  epigraph t at loss as shared
  epigraph s at penalty as recovered

example : GlobalEquivalence source lateFailure := lateFailureAlias

end
end MorewTest.Reformulation.OccurrenceFailures
