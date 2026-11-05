/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.RemoveInstances

/-! # Imported removal continues to distinguish captured order instances -/

namespace MorewTest.Reformulation.ImportedRemoveInstances

open Morew RemoveInstances
noncomputable section
set_option linter.overlappingInstances false

section
variable {X : Type*} [first : Preorder X] [second : Preorder X] [third : Preorder X]
variable (f : Preorder X → X → X)

reformulation continued : (@partialRemoval X first second f) := by
  remove at second_order

example : @continued X first second f = @completeRemoval X first second f := rfl
example : GlobalEquiv (@source X first second f) (@continued X first second f) :=
  (@partialRemoval.equiv X first second f).trans (@continued.equiv X first second f)
end

section
variable [first : LinearOrder ℝ] [second : LinearOrder ℝ]
variable (f : LinearOrder ℝ → ℝ → ℝ)

reformulation continuedSquare : (@squareOperandRemoved first f) := by
  remove at tag

example (x : ℝ) : (@continuedSquare first f).objective x = f first x := rfl
example (x : ℝ) : (@continuedSquare first f).feasible x ↔ True := Iff.rfl
example : GlobalEquiv (squareOperandSource first f) (@continuedSquare first f) :=
  (@squareOperandRemoved.equiv first f).trans (@continuedSquare.equiv first f)
end

end
end MorewTest.Reformulation.ImportedRemoveInstances
