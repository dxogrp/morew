/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support
import MorewTest.Affine.HelperFixtures

/-!
# Deterministic helper expansion limits

Expansion budgets constrain helper unfolding, while native affine expressions
remain certifiable even when unfolding is disabled.
-/

namespace MorewTest.Affine.HelperLimits

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Affine MorewTest.Affine HelperFixtures

private noncomputable def duplicate (x : ℝ) : ℝ := x + x + x + x

private noncomputable def duplicateLet (x : ℝ) : ℝ :=
  let y := x + x + x + x + x + x + x + x
  y + y + y + y

private def applyHelper (f : ℝ → ℝ) (x : ℝ) : ℝ := f x

private def assertLimit (term : TSyntax `term) (kind : String) : TermElabM Unit := do
  let expression ← elaborate term
  match ← reifyAffine expression with
  | .ok _ => throwError "helper expansion exceeded its {kind} budget"
  | .error error =>
    let message := (← error.reason.toString).toLower
    unless message.contains "limit" && message.contains kind do
      throwError "expected an expansion-{kind} limit diagnostic, got: {message}"

set_option morew.affine.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => 2 * x + 1))
  assertUnsupported (← `(fun x : ℝ => cost 2 1 x))

set_option morew.affine.maxExpansionDepth 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => cost 2 1 x))
  assertLimit (← `(fun x : ℝ => nestedCost 2 1 x)) "depth"
  assertLimit (← `(fun x : ℝ => shift (shift x))) "depth"

set_option morew.affine.maxExpansionDepth 3 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => nestedCost 2 1 x))
  assertAffine (← `(fun x : ℝ => shift (shift x)))

set_option morew.affine.maxExpansionSteps 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => 2 * x + 1))
  assertUnsupported (← `(fun x : ℝ => cost 2 1 x))

set_option morew.affine.maxExpansionSteps 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => cost 2 1 x))
  assertLimit (← `(fun x : ℝ => cost 2 1 x + cost 3 1 x)) "step"

set_option morew.affine.maxExpansionSteps 2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => cost 2 1 x + cost 3 1 x))

set_option morew.affine.maxExpansionNodes 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => 2 * x + 1))
  assertUnsupported (← `(fun x : ℝ => cost 2 1 x))

set_option morew.affine.maxExpansionNodes 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun x : ℝ => cost 2 1 x)) "node"

set_option morew.affine.maxExpansionNodes 1000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => nestedCost 2 1 x))

/-! The input fits the limit, but substituting its argument four times does not.
The smaller budget must reject before constructing that larger expression. -/

set_option morew.affine.maxExpansionNodes 200 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let term ← `(fun x : ℝ => duplicate (x + x + x + x + x + x + x + x))
  unless (← elaborate term).sizeWithoutSharing < 200 do
    throwError "duplication regression no longer starts below the node limit"
  assertLimit term "node"

set_option morew.affine.maxExpansionNodes 1000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let term ← `(fun x : ℝ => duplicate (x + x + x + x + x + x + x + x))
  let source ← elaborate term
  let prepared ← Expansion.prepare source fun expression preserve =>
    reduceStructure expression preserve
  unless prepared.expression.sizeWithoutSharing > 200 do
    throwError "duplication regression no longer expands beyond the smaller limit"
  assertAffine term

/-! Reusing a helper-local let must charge each substituted occurrence too. -/

set_option morew.affine.maxExpansionNodes 200 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun x : ℝ => duplicateLet x)) "node"

set_option morew.affine.maxExpansionNodes 1000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ => duplicateLet x))

/-! A helper may expose a second beta reduction that duplicates the argument. -/

set_option morew.affine.maxExpansionNodes 200 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let term ← `(fun x : ℝ =>
    applyHelper (fun y => y + y + y + y) (x + x + x + x + x + x + x + x))
  unless (← elaborate term).sizeWithoutSharing < 200 do
    throwError "higher-order duplication regression no longer starts below the node limit"
  assertLimit term "node"

set_option morew.affine.maxExpansionNodes 1000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ =>
    applyHelper (fun y => y + y + y + y) (x + x + x + x + x + x + x + x)))

/-! A failed attempt must not consume the budget of a later independent call. -/

set_option morew.affine.maxExpansionSteps 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun x : ℝ => nestedCost 2 1 x)) "step"
  assertAffine (← `(fun x : ℝ => cost 2 1 x))

end MorewTest.Affine.HelperLimits
