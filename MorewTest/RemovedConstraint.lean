/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform

/-!
# Generic constraint-removal semantics

Removal needs only an exact decomposition and an implication from the retained
predicate. Decision points and objective values are unchanged in both directions;
neither the constructor nor its equivalence needs decision-space structure.
-/

namespace MorewTest.RemovedConstraint

open Morew

universe u v

section Unordered

variable {X : Type u} {V : Type v} {selected : X → Prop}
    (p : Problem X V) (decomposition : ConstraintDecomposition p selected)

example : Problem X V := p.removeConstraint decomposition

example (point : X) :
    (p.removeConstraint decomposition).objective point = p.objective point := rfl

example (point : X) :
    (p.removeConstraint decomposition).feasible point ↔ decomposition.remainder point := Iff.rfl

end Unordered

section Ordered

variable {X : Type u} {V : Type v} [Preorder V] {selected : X → Prop}
    (p : Problem X V) (decomposition : ConstraintDecomposition p selected)
    (implied : ∀ point, decomposition.remainder point → selected point)

example : GlobalEquivalence p (p.removeConstraint decomposition) :=
  removeConstraintEquivalence p decomposition implied

example (point : FeasiblePoint p) :
    ((removeConstraintEquivalence p decomposition implied).forward.map point).1 = point.1 := rfl

example (point : FeasiblePoint (p.removeConstraint decomposition)) :
    ((removeConstraintEquivalence p decomposition implied).backward.map point).1 = point.1 := rfl

example (point : FeasiblePoint p) :
    (p.removeConstraint decomposition).objective
      ((removeConstraintEquivalence p decomposition implied).forward.map point).1 =
        p.objective point.1 := rfl

example (point : FeasiblePoint (p.removeConstraint decomposition)) :
    p.objective ((removeConstraintEquivalence p decomposition implied).backward.map point).1 =
      (p.removeConstraint decomposition).objective point.1 := rfl

example (point : FeasiblePoint p) :
    (removeConstraintEquivalence p decomposition implied).backward.map
      ((removeConstraintEquivalence p decomposition implied).forward.map point) = point := rfl

example (point : FeasiblePoint (p.removeConstraint decomposition)) :
    (removeConstraintEquivalence p decomposition implied).forward.map
      ((removeConstraintEquivalence p decomposition implied).backward.map point) = point := rfl

-- The same implication certifies a maximum, using the dual objective order.
private def dualDecomposition : ConstraintDecomposition p.orderDual selected where
  remainder := decomposition.remainder
  feasible_iff := decomposition.feasible_iff

example : GlobalEquivalence p.orderDual
    (p.orderDual.removeConstraint (dualDecomposition p decomposition)) :=
  removeConstraintEquivalence p.orderDual (dualDecomposition p decomposition) implied

example (point : FeasiblePoint p.orderDual) :
    ((removeConstraintEquivalence p.orderDual
      (dualDecomposition p decomposition) implied).forward.map point).1 = point.1 := rfl

-- Sequential deletion requires a new implication from the updated remainder.
variable {nextSelected : X → Prop}
    (nextDecomposition : ConstraintDecomposition (p.removeConstraint decomposition) nextSelected)
    (nextImplied : ∀ point, nextDecomposition.remainder point → nextSelected point)

example : GlobalEquivalence p
    ((p.removeConstraint decomposition).removeConstraint nextDecomposition) :=
  (removeConstraintEquivalence p decomposition implied).trans
    (removeConstraintEquivalence _ nextDecomposition nextImplied)

example (point : FeasiblePoint p) :
    (((removeConstraintEquivalence p decomposition implied).trans
      (removeConstraintEquivalence _ nextDecomposition nextImplied)).forward.map point).1 =
        point.1 := rfl

end Ordered

section TautologyAndInfeasibility

variable {X : Type u} {V : Type v} [Preorder V] (objective : X → V)

private def tautologyDecomposition :
    ConstraintDecomposition (Problem.mk objective (fun _ => True)) (fun _ => True) where
  remainder _ := True
  feasible_iff _ := ⟨fun h => ⟨h, h⟩, And.left⟩

example : GlobalEquivalence (Problem.mk objective (fun _ => True))
    ((Problem.mk objective (fun _ => True)).removeConstraint (tautologyDecomposition objective)) :=
  removeConstraintEquivalence _ _ (fun _ _ => True.intro)

-- Contradictory retained constraints can justify any selected row, without
-- inventing a feasible source point or requiring an inhabitant of X.
private def infeasibleDecomposition (selected : X → Prop) :
    ConstraintDecomposition (Problem.mk objective (fun _ => False)) selected where
  remainder _ := False
  feasible_iff _ := ⟨False.elim, And.left⟩

example (selected : X → Prop) :
    GlobalEquivalence (Problem.mk objective (fun _ => False))
      ((Problem.mk objective (fun _ => False)).removeConstraint
        (infeasibleDecomposition objective selected)) :=
  removeConstraintEquivalence _ _ (fun _ impossible => False.elim impossible)

-- Merely being infeasible is insufficient to discard the contradictory row
-- itself: the proposed retained predicate here is True.
private def necessaryDecomposition :
    ConstraintDecomposition (Problem.mk (fun _ : Unit => ()) (fun _ => False))
      (fun _ => False) where
  remainder _ := True
  feasible_iff _ := ⟨False.elim, And.right⟩

example : ¬(∀ point, necessaryDecomposition.remainder point → False) := by
  intro implication
  exact implication () True.intro

end TautologyAndInfeasibility

end MorewTest.RemovedConstraint
