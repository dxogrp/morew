/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Model-local definitions

Definitions retain binding identity in source presentations, generated targets,
and applied sources, including when distinct definitions have equal values.
-/

namespace MorewTest.Surface.LocalDefinitions

open Morew
noncomputable section

def namedModel :=
  problem (x : ℝ)
    let loss : ℝ := (x - 1) ^ 2
    let penalty := |x|
    let total := loss + penalty
    minimize total
    subject to
      cap : loss + penalty ≤ 10

example (x : ℝ) : namedModel.objective x = (x - 1) ^ 2 + |x| := rfl
example (x : ℝ) : namedModel.feasible x ↔ (x - 1) ^ 2 + |x| ≤ 10 := Iff.rfl

-- The objective determines the function's type, while feasibility does not
-- use it. Both functions must share the same inferred local environment.
def inferredAlias :=
  problem (x : ℝ)
    let identity := fun y => y
    minimize identity x

reformulation inferredLifted : inferredAlias := by
  epigraph t

example (x t : ℝ) : inferredLifted.feasible (x, t) ↔ x ≤ t := Iff.rfl

def localMaximum :=
  problem (x : ℝ)
    let score := x + 1
    maximize score

reformulation localHypograph : localMaximum := by
  hypograph t

example (x t : ℝ) : localHypograph.feasible (x, t) ↔ t ≤ x + 1 := Iff.rfl

/--
info: problem (x : ℝ)
  let loss : ℝ := (x - 1) ^ 2
  let penalty := |x|
  let total := loss + penalty
  minimize total
  subject to
    cap : loss + penalty ≤ 10
-/
#guard_msgs in
#printp namedModel

def repeatedValues (offset : ℝ) :=
  problem (x : ℝ)
    let first := (x - offset) ^ 2
    let second := (x - offset) ^ 2
    let unused := x + offset
    minimize first + second
    subject to
      cap : first ≤ 10

reformulation lifted : namedModel := by
  epigraph t

example : GlobalEquivalence namedModel lifted := lifted.equivalence

example (x t : ℝ) : lifted.objective (x, t) = t := rfl
example (x t : ℝ) : lifted.feasible (x, t) ↔
    ((x - 1) ^ 2 + |x| ≤ 10) ∧ ((x - 1) ^ 2 + |x| ≤ t) := Iff.rfl

/--
info: problem (x t : ℝ)
  let loss : ℝ := (x - 1) ^ 2
  let penalty := |x|
  let total := loss + penalty
  minimize t
  subject to
    cap : loss + penalty ≤ 10
    epigraph_t : total ≤ t
-/
#guard_msgs in
#printp lifted

reformulation applied : (repeatedValues 2) := by
  epigraph t

/--
info: problem (x t : ℝ)
  let first := (x - 2) ^ 2
  let second := (x - 2) ^ 2
  let unused := x + 2
  minimize t
  subject to
    cap : first ≤ 10
    epigraph_t : first + second ≤ t
-/
#guard_msgs in
#printp applied

/-- error: duplicate model-local definition name `loss` -/
#guard_msgs in
def duplicate :=
  problem (x : ℝ)
    let loss := x ^ 2
    let loss := |x|
    minimize loss

/-- error: model-local definition `x` conflicts with a decision variable -/
#guard_msgs in
def shadowsDecision :=
  problem (x : ℝ)
    let x := x ^ 2
    minimize x

/-- error: model-local definition `coefficient` conflicts with an outer parameter -/
#guard_msgs in
def shadowsParameter (coefficient : ℝ) :=
  problem (x : ℝ)
    let coefficient := x ^ 2
    minimize coefficient

end
end MorewTest.Surface.LocalDefinitions
