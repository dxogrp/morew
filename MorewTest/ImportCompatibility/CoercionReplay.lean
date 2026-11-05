/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.ImportCompatibility.CoercionReplay.Defined

/-!
# Coercion identity across presentation reconstruction

Ambient instances and pretty-printing options cannot change a source's explicit
coercion functions, elaborated casts, local definitions, or decision types.
-/

namespace MorewTest.ImportCompatibility.CoercionReplay

open Morew Defined
noncomputable section

local instance (priority := high) : Coe Box ℝ := ⟨fun box => -box.value⟩
local instance (priority := high) : Coe Box ℕ := ⟨fun box => box.size + 1⟩

example (box : Box) : (box : ℝ) = -box.value := rfl
example (box : Box) : (box : ℕ) = box.size + 1 := rfl

-- Explicitly enabling notation must not override the internal elaboration options.
set_option pp.coercions true

reformulation explicitCopy : explicitSource := by

example : GlobalEquiv explicitSource explicitCopy := explicitCopy.equiv
example (x : Box) : explicitCopy.objective x = x.value := rfl

reformulation castCopy : castSource := by

example : GlobalEquiv castSource castCopy := castCopy.equiv
example (x : Box) : castCopy.objective x = x.value := rfl

-- The selector, retained row, and new bound must all use the source's function.
reformulation expressionLift : explicitSource := by
  epigraph t at (boxToReal x)

example : GlobalEquiv explicitSource expressionLift := expressionLift.equiv
example (x : Box) (t : ℝ) : expressionLift.objective (x, t) = t := rfl
example (x : Box) (t : ℝ) : expressionLift.feasible (x, t) ↔ x.value ≤ t := Iff.rfl

reformulation namedLift : (family 3) := by
  epigraph t at loss

example : GlobalEquiv (family 3) namedLift := namedLift.equiv
example (x : Box) (t : ℝ) : namedLift.objective (x, t) = t + 3 := rfl
example (x : Box) (t : ℝ) : namedLift.feasible (x, t) ↔
    x.value ≤ 10 ∧ x.value ≤ t := Iff.rfl

-- Cross both an import boundary and a previously generated declaration.
reformulation continued : generated := by
  epigraph s at (boxToReal x) in cap

example : GlobalEquiv generated continued := continued.equiv
example (x : Box) (t s : ℝ) : continued.objective ((x, t), s) = t + 2 := rfl
example (x : Box) (t s : ℝ) : continued.feasible ((x, t), s) ↔
    s ≤ 10 ∧ x.value ≤ t ∧ x.value ≤ s := Iff.rfl

section
variable (box : Box)

-- Re-elaborating a decision type must not resynthesize the natural-number coercion.
reformulation indexedCopy : (indexedFamily box) := by

example : GlobalEquiv (indexedFamily box) (indexedCopy box) :=
  indexedCopy.equiv box
example (i : Fin (box.size + 1)) : (indexedCopy box).objective i = (i.val : ℝ) := rfl

end
end
end MorewTest.ImportCompatibility.CoercionReplay
