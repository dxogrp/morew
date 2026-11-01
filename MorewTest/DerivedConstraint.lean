/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform

/-!
# Generic derived-constraint semantics

Constraint addition needs no structure on the decision or objective types.
Its exactness certificate uses only a preorder on objective values and keeps
the underlying decision point in both directions, including after composition.
-/

namespace MorewTest.DerivedConstraint

open Morew

universe u v

section Unordered

variable {X : Type u} {V : Type v} (p : Problem X V) (constraint : X → Prop)

example : Problem X V := p.addConstraint constraint

example (point : X) :
    (p.addConstraint constraint).objective point = p.objective point := rfl

example (point : X) :
    (p.addConstraint constraint).feasible point ↔
      p.feasible point ∧ constraint point := Iff.rfl

end Unordered

section Ordered

variable {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) (constraint : X → Prop)
    (implied : ∀ point, p.feasible point → constraint point)

example : GlobalEquivalence p (p.addConstraint constraint) :=
  addConstraintEquivalence p constraint implied

example (point : FeasiblePoint p) :
    ((addConstraintEquivalence p constraint implied).forward.map point).1 = point.1 := rfl

example (point : FeasiblePoint (p.addConstraint constraint)) :
    ((addConstraintEquivalence p constraint implied).backward.map point).1 = point.1 := rfl

example (point : FeasiblePoint p) :
    (addConstraintEquivalence p constraint implied).backward.map
      ((addConstraintEquivalence p constraint implied).forward.map point) = point := by
  rfl

example (point : FeasiblePoint (p.addConstraint constraint)) :
    (addConstraintEquivalence p constraint implied).forward.map
      ((addConstraintEquivalence p constraint implied).backward.map point) = point := by
  rfl

-- A later implication can use the already derived constraint. Composing the
-- resulting certificates still preserves the original point and objective.
variable (nextConstraint : X → Prop)
    (nextImplied : ∀ point, p.feasible point → constraint point → nextConstraint point)

private def chained :
    GlobalEquivalence p ((p.addConstraint constraint).addConstraint nextConstraint) :=
  (addConstraintEquivalence p constraint implied).trans
    (addConstraintEquivalence (p.addConstraint constraint) nextConstraint
      (fun point feasible => nextImplied point feasible.1 feasible.2))

example (point : FeasiblePoint p) :
    ((chained p constraint implied nextConstraint nextImplied).forward.map point).1 =
      point.1 := rfl

example (point : FeasiblePoint ((p.addConstraint constraint).addConstraint nextConstraint)) :
    ((chained p constraint implied nextConstraint nextImplied).backward.map point).1 =
      point.1 := rfl

example (point : FeasiblePoint p) :
    ((p.addConstraint constraint).addConstraint nextConstraint).objective
      ((chained p constraint implied nextConstraint nextImplied).forward.map point).1 =
        p.objective point.1 := rfl

-- Maximization uses the same constructor and certificate over the dual order.
example : GlobalEquivalence p.orderDual (p.orderDual.addConstraint constraint) :=
  addConstraintEquivalence p.orderDual constraint implied

example (point : FeasiblePoint p.orderDual) :
    ((addConstraintEquivalence p.orderDual constraint implied).forward.map point).1 =
      point.1 := rfl

end Ordered

section EmptyAndInfeasible

variable {X : Type u} {V : Type v} [Preorder V] (objective : X → V)

-- Explicit tautologies remain predicates of the constructed problem.
example :
    GlobalEquivalence (Problem.mk objective (fun _ => True))
      ((Problem.mk objective (fun _ => True)).addConstraint (fun _ => True)) :=
  addConstraintEquivalence _ _ (fun _ _ => True.intro)

example (constraint : X → Prop) :
    GlobalEquivalence (Problem.mk objective (fun _ => False))
      ((Problem.mk objective (fun _ => False)).addConstraint constraint) :=
  addConstraintEquivalence _ _ (fun _ impossible => False.elim impossible)

end EmptyAndInfeasible

end MorewTest.DerivedConstraint
