/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic

/-! # Removal uses captured operations without treating operand data as instances -/

namespace MorewTest.Reformulation.RemoveInstances

open Morew
noncomputable section
set_option linter.overlappingInstances false

section
variable {X : Type*} [first : Preorder X] [second : Preorder X]
variable (f : Preorder X → X → X)

def source :=
  problem (x : X)
    minimize (0 : Nat)
    subject to
      first_order : @LE.le X first.toLE x x
      second_order : @GE.ge X second.toLE x x
      operand : @LE.le X first.toLE (f second x) (f second x)
      retained : @LE.le X first.toLE x (f second x)

-- The second order is both a competing local instance and ordinary operand
-- data. Neither use changes which order proves the first and third rows.
reformulation partialRemoval : (@source X first second f) := by
  remove at first_order
  remove at operand

reformulation completeRemoval : (@source X first second f) := by
  remove at first_order
  remove at second_order
  remove at operand

example (x : X) : (@partialRemoval X first second f).feasible x ↔
    @GE.ge X second.toLE x x ∧ @LE.le X first.toLE x (f second x) := Iff.rfl
example (x : X) : (@completeRemoval X first second f).feasible x ↔
    @LE.le X first.toLE x (f second x) := Iff.rfl
example : GlobalEquivalence (@source X first second f) (@completeRemoval X first second f) :=
  @completeRemoval.equivalence X first second f
end

-- These models capture the ordinary real order before any shadowing instance
-- is introduced. The explicit order parameter is data passed to `f` only.
def squareSource :=
  problem (x : ℝ)
    minimize (0 : Nat)
    subject to
      square : 0 ≤ x ^ 2
      tag : True

def squareOperandSource (order : LinearOrder ℝ) (f : LinearOrder ℝ → ℝ → ℝ) :=
  problem (x : ℝ)
    minimize f order x
    subject to
      square : 0 ≤ (f order x) ^ 2
      tag : True

section
variable [shadow : LinearOrder ℝ] (f : LinearOrder ℝ → ℝ → ℝ)

reformulation squareRemoved : squareSource := by
  remove at square

reformulation squareOperandRemoved : (squareOperandSource shadow f) := by
  remove at square

example (x : ℝ) : squareRemoved.feasible x ↔ True := Iff.rfl
example (x : ℝ) : (@squareOperandRemoved shadow f).feasible x ↔ True := Iff.rfl
example (x : ℝ) : (@squareOperandRemoved shadow f).objective x = f shadow x := rfl
example : GlobalEquivalence squareSource squareRemoved := squareRemoved.equivalence
example : GlobalEquivalence (squareOperandSource shadow f) (@squareOperandRemoved shadow f) :=
  squareOperandRemoved.equivalence f
end

end
end MorewTest.Reformulation.RemoveInstances
