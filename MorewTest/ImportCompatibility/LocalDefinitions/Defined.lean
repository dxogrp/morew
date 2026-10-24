/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! Model-local bindings exported across a compiled module boundary. -/

namespace MorewTest.ImportCompatibility.LocalDefinitions.Defined

open Morew
noncomputable section

namespace External

def score (offset x : ℝ) : ℝ := (x - offset) ^ 2

end External

open External

def family (offset : ℝ) :=
  problem (x : ℝ)
    let loss := score offset x
    let same := score offset x
    let total := loss + same
    let unused := x + offset
    minimize total
    subject to
      cap : loss ≤ 10

section

variable (offset : ℝ)

reformulation generated : (family offset) := by
  epigraph t

end

def affine :=
  problem (x : ℝ)
    let score := x + 3
    let magnitude := |x|
    minimize score
    subject to
      cap : magnitude ≤ 10

reformulation terminal : affine := by
  conic

universe u

def generic (α : Type u) [Preorder α] (witness : True) :=
  problem (x : α)
    let label : α := x
    let evidence := witness
    minimize label

def shadowedFamily (a b : ℝ) :=
  problem (x : ℝ)
    let loss := a - b + x
    minimize loss

opaque proofCoefficient (_ : ∃ n : Nat, n = n) : ℝ := 7

def proofFamily (n : Nat) :=
  problem (x : ℝ)
    let loss := proofCoefficient ⟨n, rfl⟩ + x
    minimize loss

end
end MorewTest.ImportCompatibility.LocalDefinitions.Defined
