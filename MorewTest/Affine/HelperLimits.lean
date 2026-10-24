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

private noncomputable def projectedDuplicate : (ℝ → ℝ) × ℝ :=
  ((fun y => y + y + y + y), 0)

private noncomputable def projectedApply : ((ℝ → ℝ) → ℝ → ℝ) × ℝ :=
  ((fun f y => f y), 0)

private noncomputable def problemDuplicate (f : Fin 2 → ℝ) :
    Morew.Problem (Fin 2) ℝ :=
  ⟨f + f + f + f, fun _ => True⟩

private noncomputable def projectedProblemDuplicate (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (problemDuplicate f).objective

private noncomputable def pairedProblemDuplicate (f : Fin 2 → ℝ) :
    Morew.Problem (Fin 2) ℝ × Unit :=
  (problemDuplicate f, ())

private noncomputable def projectedPairedProblemDuplicate (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (pairedProblemDuplicate f).1.objective

private noncomputable def problemWithOtherHelpers (f : Fin 2 → ℝ) :
    Morew.Problem (Fin 2) ℝ :=
  ⟨f, fun i => nestedCost 2 1 (f i) ≤ 0⟩

private noncomputable def projectedProblemObjective (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (problemWithOtherHelpers f).objective

private noncomputable def problemWithSelectedHelper (f : Fin 2 → ℝ) :
    Morew.Problem (Fin 2) ℝ :=
  ⟨fun i => cost 2 1 (f i), fun _ => True⟩

private noncomputable def projectedProblemHelper (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  (problemWithSelectedHelper f).objective

private noncomputable def letProjectedProblemHelper (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  let problem := problemWithSelectedHelper f
  problem.objective

private noncomputable def problemReturningProblem (f : Fin 2 → ℝ) :
    Morew.Problem Unit (Morew.Problem (Fin 2) ℝ) :=
  ⟨fun _ => problemDuplicate f, fun _ => True⟩

private noncomputable def projectedNestedProblemDuplicate (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ((problemReturningProblem f).objective ()).objective

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

/-! Expanding a projected function must charge the beta reduction exposed when
the projection and application are rebuilt, including successive applications. -/

set_option morew.affine.maxExpansionNodes 200 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let term ← `(fun x : ℝ =>
    projectedDuplicate.1 (x + x + x + x + x + x + x + x))
  unless (← elaborate term).sizeWithoutSharing < 200 do
    throwError "projected duplication regression no longer starts below the node limit"
  assertLimit term "node"
  assertLimit (← `(fun x : ℝ =>
    projectedApply.1 duplicate (x + x + x + x + x + x + x + x))) "node"

set_option morew.affine.maxExpansionNodes 1000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ =>
    projectedDuplicate.1 (x + x + x + x + x + x + x + x)))
  assertAffine (← `(fun x : ℝ =>
    projectedApply.1 duplicate (x + x + x + x + x + x + x + x)))

-- The equivalent helper-free expression still succeeds through direct recognition.
set_option morew.affine.maxExpansionNodes 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : ℝ =>
    ((fun y : ℝ => y + y + y + y), (0 : ℝ)).1
      (x + x + x + x + x + x + x + x)))

/-! A helper can expose a problem projection whose container expands into a
large native objective. Opening that container must consume the same budget. -/

set_option morew.affine.maxExpansionNodes 100 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let term ← `(fun x : Fin 2 → ℝ => projectedProblemDuplicate x)
  unless (← elaborate term).sizeWithoutSharing < 100 do
    throwError "problem projection regression no longer starts below the node limit"
  assertLimit term "node"
  assertLimit (← `(fun x : Fin 2 → ℝ => projectedNestedProblemDuplicate x)) "node"

set_option morew.affine.maxExpansionNodes 1000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let term ← `(fun x : Fin 2 → ℝ => projectedProblemDuplicate x)
  let source ← elaborate term
  let prepared ← Expansion.prepare source fun expression preserve =>
    reduceStructure expression preserve
  unless prepared.expression.sizeWithoutSharing > 100 do
    throwError "problem projection regression no longer expands beyond the smaller limit"
  assertAffine term
  assertAffine (← `(fun x : Fin 2 → ℝ => projectedPairedProblemDuplicate x))
  assertAffine (← `(fun x : Fin 2 → ℝ => projectedNestedProblemDuplicate x))

set_option morew.affine.maxExpansionDepth 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun x : Fin 2 → ℝ => projectedProblemDuplicate x)) "depth"

set_option morew.affine.maxExpansionDepth 2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ => projectedProblemDuplicate x))
  assertLimit (← `(fun x : Fin 2 → ℝ => projectedProblemHelper x)) "depth"
  assertLimit (← `(fun x : Fin 2 → ℝ => letProjectedProblemHelper x)) "depth"

set_option morew.affine.maxExpansionDepth 3 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ => projectedProblemHelper x))
  assertAffine (← `(fun x : Fin 2 → ℝ => letProjectedProblemHelper x))

set_option morew.affine.maxExpansionSteps 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun x : Fin 2 → ℝ => projectedProblemDuplicate x)) "step"

set_option morew.affine.maxExpansionSteps 2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ => projectedProblemDuplicate x))
  -- Helpers in the unselected feasible field do not consume expansion steps.
  assertAffine (← `(fun x : Fin 2 → ℝ => projectedProblemObjective x))

-- Existing direct problem projections still certify without helper expansion.
set_option morew.affine.maxExpansionNodes 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertAffine (← `(fun x : Fin 2 → ℝ => (problemDuplicate x).objective))

/-! A failed attempt must not consume the budget of a later independent call. -/

set_option morew.affine.maxExpansionSteps 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun x : ℝ => nestedCost 2 1 x)) "step"
  assertAffine (← `(fun x : ℝ => cost 2 1 x))

end MorewTest.Affine.HelperLimits
