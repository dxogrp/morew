/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic
import MorewTest.Surface.Conic
import Morew.Reformulation

/-!
# Affine recognition from existing surface presentations

These regressions consume the same typed objective projections and predicates
used by the reformulation runner, without installing a conic surface command.
-/

namespace MorewTest.Surface.Affine

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew

noncomputable section

def minimum : Problem ℝ ℝ :=
  problem (x : ℝ)
    minimize 2 * x + 1
    subject to
      lower : x ≥ 0
      upper : x + 1 ≤ 4

def maximum : Problem ℝ (OrderDual ℝ) :=
  problem (x : ℝ)
    maximize (-x + 2 : ℝ)
    subject to
      lower : x ≥ 0
      upper : x + 1 ≤ 4

def customCost (x : ℝ) : ℝ := x + 1

def grouped : Problem (ℝ × ℝ) ℝ :=
  problem (x y : ℝ)
    minimize 2 * x - y
    subject to
      total : x + y = 4
      lower : x ≥ 0

reformulation groupedEpigraph : grouped := by
  epigraph t

def customObjective : Problem ℝ ℝ :=
  problem (x : ℝ)
    minimize customCost x
    subject to
      upper : x ≤ 4

private def checkSource (name : Name) (sense : ObjectiveSense)
    (acceptedObjective : Bool) : TermElabM Unit := do
  let source := Lean.mkConst name
  let some view := Morew.Syntax.getProblemView? (← getEnv) name
    | throwError "missing source presentation"
  let projection ← mkAppM ``Problem.objective #[source]
  let direct ← Morew.Elab.Affine.reifyAffine projection
  match direct, acceptedObjective with
  | .ok result, true => checkWithKernel result.pointwiseEquality
  | .error _, false => pure ()
  | .error error, true => throwError "source objective projection failed: {error.reason}"
  | .ok _, false => throwError "source extraction unfolded a custom objective helper"
  let some sourceValue ← unfoldDefinition? source
    | throwError "could not inspect source declaration"
  let presentation ←
    Morew.Reformulation.Internal.typedPresentationFromExpression sourceValue view
  unless presentation.sense == sense do
    throwError "typed presentation lost the objective sense"
  if sense == .maximize then
    unless presentation.valueType.isAppOfArity ``OrderDual 1 do
      throwError "typed presentation lost its explicit order-dual objective type"
  let typedObjective ← Morew.Elab.Conic.reifyObjective presentation
  match typedObjective, acceptedObjective with
  | .ok result, true => checkWithKernel result.pointwiseEquality
  | .error error, false =>
    unless (← error.reason.toString).contains "objective" do
      throwError "missing objective context for a custom helper"
  | .error error, true => throwError "typed objective projection failed: {error.reason}"
  | .ok _, false => throwError "typed extraction unfolded a custom objective helper"
  unless presentation.constraints.size == view.constraints.size do
    throwError "typed presentation changed the row count"
  for entry in presentation.constraints do
    match ← Morew.Elab.Conic.normalizeConstraint entry with
    | .ok result => checkWithKernel result.pointwiseIff
    | .error error => throwError "typed constraint failed: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  checkSource ``minimum .minimize true
  checkSource ``maximum .maximize true
  checkSource ``customObjective .minimize false
  checkSource ``grouped .minimize true
  checkSource ``groupedEpigraph .minimize true
  checkSource ``MorewTest.Surface.Conic.minimum .minimize true
  checkSource ``MorewTest.Surface.Conic.maximum .maximize true
  checkSource ``MorewTest.Surface.Conic.minimumEpigraph .minimize true
  checkSource ``MorewTest.Surface.Conic.maximumHypograph .maximize true

end

end MorewTest.Surface.Affine
