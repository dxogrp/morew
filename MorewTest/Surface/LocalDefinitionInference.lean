/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Inferred decision types with model-local definitions

The decision domain and the local binders must share inference variables, both
when the declaration supplies the domain and when the bodies determine it.
-/

namespace MorewTest.Surface.LocalDefinitionInference

open Morew
noncomputable section

def inferredMinimum : Problem ℝ ℝ :=
  problem (x : _)
    let loss := x
    minimize loss

example (x : ℝ) : inferredMinimum.objective x = x := rfl

reformulation minimumLifted : inferredMinimum := by
  epigraph t at loss

example (x t : ℝ) : minimumLifted.objective (x, t) = t := rfl
example (x t : ℝ) : minimumLifted.feasible (x, t) ↔ x ≤ t := Iff.rfl

def inferredMaximum : Problem ℝ (OrderDual ℝ) :=
  problem (x : _)
    let score := x + 1
    maximize score

reformulation maximumLifted : inferredMaximum := by
  hypograph t

example (x t : ℝ) : maximumLifted.feasible (x, t) ↔ t ≤ x + 1 := Iff.rfl

-- The product domain supplies distinct types to grouped and separate binders.
def grouped : Problem ((ℝ × ℝ) × Nat) ℝ :=
  problem (x y : _) (n : _)
    let total := x + y + (n : ℝ)
    minimize total
    subject to cap : x ≤ y

reformulation groupedLifted : grouped := by
  epigraph t

example (x y t : ℝ) (n : Nat) :
    groupedLifted.feasible (((x, y), n), t) ↔
      x ≤ y ∧ x + y + (n : ℝ) ≤ t := Iff.rfl

def mixed : Problem ((ℝ × Nat) × ℝ) ℝ :=
  problem (x : _) (n : Nat) (y : _)
    let total := x + (n : ℝ) + y
    minimize total

example (x y : ℝ) (n : Nat) : mixed.objective ((x, n), y) =
    x + (n : ℝ) + y := rfl

-- One decision can itself be a product; its type must remain intact.
def pairDecision : Problem (ℝ × ℝ) ℝ :=
  problem (xy : _)
    let total := xy.1 + xy.2
    minimize total

reformulation pairLifted : pairDecision := by
  epigraph t

example (x y t : ℝ) : pairLifted.feasible ((x, y), t) ↔ x + y ≤ t := Iff.rfl

-- Partial annotations share the domain's inferred indices as well as types.
def indexed : Problem (Fin 3) Nat :=
  problem (i : Fin _)
    let value := i.val
    minimize value

example (i : Fin 3) : indexed.objective i = i.val := rfl

-- Without a declaration annotation, the objective and definitions can infer
-- the same decision-domain variables before projections are constructed.
def fromObjective :=
  problem (x : _)
    let loss := x
    minimize (loss : ℝ)

example (x : ℝ) : fromObjective.objective x = x := rfl

def fromDefinitions :=
  problem (x : _) (n : _)
    let realValue : ℝ := x
    let naturalValue : Nat := n
    minimize realValue + (naturalValue : ℝ)

reformulation definitionsLifted : fromDefinitions := by
  epigraph t

example (x t : ℝ) (n : Nat) : definitionsLifted.feasible ((x, n), t) ↔
    x + (n : ℝ) ≤ t := Iff.rfl

universe u

abbrev Carrier (α : Type u) := α

def generic (α : Type u) : Problem (Carrier α) α :=
  problem (x : _)
    let label : Carrier α := x
    minimize label

section
variable (α : Type u) [Preorder α]

reformulation genericLifted : (generic α) := by
  epigraph t

example (x t : α) : (genericLifted α).feasible (x, t) ↔ x ≤ t := Iff.rfl

end
end
end MorewTest.Surface.LocalDefinitionInference
