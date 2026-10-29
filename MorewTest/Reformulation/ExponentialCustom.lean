/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Custom exact exponential representations

All four certificate families may emit single or grouped exponential rows.
Unit auxiliaries disappear; scalar and vector auxiliaries extend the original
domain once. Invalid explicit certificates never fall back to automatic rules.
-/

namespace MorewTest.Reformulation.ExponentialCustom

open Morew Morew.Conic

noncomputable section

private theorem boundary (x : ℝ) : (0, 0, x) ∈ EXP ↔ 0 ≤ x := by simp

def userIdentity (x : ℝ) : ℝ := x

def graphRule : GraphRepresentation userIdentity where
  Auxiliary := Unit
  target x y _ :=
    let difference := y - x
    True ∧ (0, 0, difference) ∈ EXP ∧
      ((∀ _ : Fin 1, (0, 0, x - y) ∈ EXP) ∧ True)
  source_iff_exists x y := by
    simp only [userIdentity, boundary, sub_nonneg, and_true, true_and, exists_const,
      forall_const]
    exact eq_comm.trans le_antisymm_iff

def epigraphRule : EpigraphRepresentation Fn.softplus where
  Auxiliary := Fin 2 → ℝ
  target x t u := (∀ i : Fin 2, (![0, x] i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1
  source_iff_exists x t := Exponential.softplus_le_iff x t

def hypographRule : HypographRepresentation userIdentity where
  Auxiliary := Unit
  target x t _ := (0, 0, x - t) ∈ EXP
  source_iff_exists x t := by
    simp only [userIdentity, boundary, sub_nonneg, exists_const]

def scalarAuxiliaryRule : ExactConstraintLift
    (fun point : ℝ × ℝ => Real.exp point.1 ≤ point.2) where
  Auxiliary := ℝ
  target point u := u = point.1 ∧
    (let bound := point.2
     True ∧ (u, 1, bound) ∈ EXP)
  source_iff_exists point := by
    simp only [true_and, exists_eq_left]
    exact Exponential.exp_le_iff point.1 point.2

def graphSource :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      graph : y = userIdentity x

reformulation graphTarget : graphSource := by
  conic at graph using graphRule

example : GlobalEquivalence graphSource graphTarget := graphTarget.equivalence

example (x y : ℝ) : graphTarget.feasible (x, y) ↔
    (0, 0, y - x) ∈ EXP ∧ (∀ _ : Fin 1, (0, 0, x - y) ∈ EXP) := Iff.rfl

def epigraphSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      epi_row : Fn.softplus x ≤ t

reformulation epigraphTarget : epigraphSource := by
  conic at epi_row using epigraphRule

example : GlobalEquivalence epigraphSource epigraphTarget := epigraphTarget.equivalence

example (x t : ℝ) (u : Fin 2 → ℝ) : epigraphTarget.feasible ((x, t), u) ↔
    (∀ i, (![0, x] i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 := Iff.rfl

def hypographSource :=
  problem (x t : ℝ)
    maximize x
    subject to
      hypo_row : t ≤ userIdentity x

reformulation hypographTarget : hypographSource := by
  conic at hypo_row using hypographRule

example : GlobalEquivalence hypographSource hypographTarget := hypographTarget.equivalence

example (x t : ℝ) : hypographTarget.feasible (x, t) ↔
    (0, 0, x - t) ∈ EXP := Iff.rfl

def source :=
  problem (x t : ℝ)
    minimize x + t
    subject to
      before : x * x ≤ 1
      exponential : Real.exp x ≤ t
      after : t ≤ 10

reformulation target : source := by
  conic at exponential using scalarAuxiliaryRule

example : GlobalEquivalence source target := target.equivalence

example (x t u : ℝ) : target.objective ((x, t), u) = x + t := rfl

example (x t u : ℝ) : target.feasible ((x, t), u) ↔
    x * x ≤ 1 ∧ u = x ∧ (u, 1, t) ∈ EXP ∧ t ≤ 10 := Iff.rfl

def emptyRule : ExactConstraintLift (fun _ : ℝ => True) where
  Auxiliary := Unit
  target x _ := ∀ _ : Fin 0, (x, 1, x) ∈ EXP
  source_iff_exists _ := by simp

def emptySource :=
  problem (x : ℝ)
    minimize x
    subject to
      before : x ≤ 1
      empty : True
      after : 0 ≤ x

reformulation emptyTarget : emptySource := by
  conic at empty using emptyRule

example : GlobalEquivalence emptySource emptyTarget := emptyTarget.equivalence

example (x : ℝ) : emptyTarget.feasible x ↔
    x ≤ 1 ∧ (∀ _ : Fin 0, (x, 1, x) ∈ EXP) ∧ 0 ≤ x := Iff.rfl

run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``emptyTarget
    | Lean.throwError "empty custom family lost its presentation"
  unless view.constraints.map (·.name) == #[`before, `empty_conic_1, `after] do
    Lean.throwError "empty custom family was dropped or expanded"

elab "assert_atomic_exponential% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  if let some name := MorewTest.newLocalDeclaration? before after then
    Lean.throwError m!"failed reformulation leaked auxiliary declaration {name}"

#guard_error_fragments ["constraint `after`: the exact representation input is not the decision space"] in
assert_atomic_exponential%
reformulation rollback : source certificate rollbackAlias := by
  conic at exponential using scalarAuxiliaryRule
  conic at after using scalarAuxiliaryRule

def automaticSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      exponential : Real.exp x ≤ t + 1

#guard_error_fragments ["constraint `exponential`: representation operation", "does not match",
  "+ 1"] in
reformulation noFallback : automaticSource := by
  conic at exponential using scalarAuxiliaryRule

def unitEpigraph : EpigraphRepresentation Real.exp where
  Auxiliary := Unit
  target x t _ := (x, 1, t) ∈ EXP
  source_iff_exists x t := by
    simpa only [exists_const] using Exponential.exp_le_iff x t

def nonlinearSource :=
  problem (x t : ℝ)
    minimize t
    subject to
      bad : Real.exp (x * x) ≤ t

/-- error: constraint `bad`: generated row -/
#guard_msgs (substring := true) in
reformulation nonlinearTarget : nonlinearSource := by
  conic at bad using unitEpigraph

def uninspectableRule : ExactConstraintLift (fun x : ℝ => 0 ≤ x) where
  Auxiliary := Unit
  target x _ := ∀ _ : Fin 1, True ∧ (0, 0, x) ∈ EXP
  source_iff_exists _ := by simp

def uninspectableSource :=
  problem (x : ℝ)
    minimize x
    subject to
      bad : 0 ≤ x

/-- error: constraint `bad`: generated row: constraint: expected one exponential membership or power membership under the finite quantifier -/
#guard_msgs (substring := true) in
reformulation uninspectableTarget : uninspectableSource := by
  conic at bad using uninspectableRule

run_cmd do
  let env ← Lean.getEnv
  for name in #[`rollback, `noFallback, `nonlinearTarget, `uninspectableTarget] do
    let full := `MorewTest.Reformulation.ExponentialCustom ++ name
    if env.contains full || env.contains (full ++ `equivalence) then
      Lean.throwError "failed custom rewrite emitted {full}"
    if (Morew.Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed custom rewrite registered presentation metadata"

end
end MorewTest.Reformulation.ExponentialCustom
