/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform.Parameterization
import Mathlib.Data.Nat.Basic

/-!
# Certified feasible-set restriction semantics

Restrictions use an arbitrary no-worse repair and inclusion in the reverse
direction. Coverage-based repairs additionally preserve the represented source
point, its objective, and every retained coordinate.
-/

namespace MorewTest.Restriction

open Morew

universe u v w x y z

section Generic

variable {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) (constraint : X → Prop)
    (repair : GlobalImprovement p (p.addConstraint constraint))

example : GlobalEquiv p (p.addConstraint constraint) :=
  restrictionEquiv p constraint repair

example (point : FeasiblePoint p) :
    (restrictionEquiv p constraint repair).forward.map point = repair.map point := rfl

example (point : FeasiblePoint (p.addConstraint constraint)) :
    ((restrictionEquiv p constraint repair).backward.map point).1 = point.1 := rfl

example (point : FeasiblePoint p) :
    constraint ((restrictionEquiv p constraint repair).forward.map point).1 :=
  (repair.map point).2.2

example (dualRepair : GlobalImprovement p.orderDual (p.orderDual.addConstraint constraint)) :
    GlobalEquiv p.orderDual (p.orderDual.addConstraint constraint) :=
  restrictionEquiv p.orderDual constraint dualRepair

-- An infeasible problem needs no inhabitant or repair choice in its domain.
example (objective : X → V) (condition : X → Prop) :
    GlobalEquiv (Problem.mk objective (fun _ => False))
      ((Problem.mk objective (fun _ => False)).addConstraint condition) :=
  restrictionEquiv _ _ {
    map := fun point => False.elim point.2
    objective_le := fun point => False.elim point.2 }

end Generic

section Dominance

private def minimum : Problem Nat Nat where
  objective := id
  feasible _ := True

private def zeroRepair : GlobalImprovement minimum (minimum.addConstraint (· = 0)) where
  map _ := ⟨0, True.intro, rfl⟩
  objective_le point := Nat.zero_le point.1

-- The discarded point is feasible, but its repaired objective is strictly better.
example : minimum.feasible 1 ∧ ¬(minimum.addConstraint (· = 0)).feasible 1 := by
  exact ⟨True.intro, fun h => Nat.one_ne_zero h.2⟩

example : (zeroRepair.map ⟨1, True.intro⟩).1 = 0 := rfl

example : minimum.objective (zeroRepair.map ⟨1, True.intro⟩).1 < minimum.objective 1 :=
  Nat.zero_lt_one

example : GlobalEquiv minimum (minimum.addConstraint (· = 0)) :=
  restrictionEquiv minimum _ zeroRepair

private def maximum : Problem Nat (OrderDual Nat) where
  objective := id
  feasible point := point ≤ 2

private def topRepair : GlobalImprovement maximum (maximum.addConstraint (· = 2)) where
  map _ := ⟨2, Nat.le_refl 2, rfl⟩
  objective_le point := point.2

-- The same API reads the objective inequality in the maximization order.
example : GlobalEquiv maximum (maximum.addConstraint (· = 2)) :=
  restrictionEquiv maximum _ topRepair

example : (topRepair.map ⟨0, Nat.zero_le 2⟩).1 = 2 := rfl

example : 0 < (topRepair.map ⟨0, Nat.zero_le 2⟩).1 :=
  Nat.zero_lt_succ 1

private def flat : Problem Bool Nat where
  objective _ := 0
  feasible _ := True

private def toggleRepair : GlobalImprovement flat (flat.addConstraint (fun _ => True)) where
  map point := ⟨!point.1, True.intro, True.intro⟩
  objective_le _ := Nat.le_refl 0

-- Even points already satisfying the restriction need not be fixed.
example : (restrictionEquiv flat _ toggleRepair).forward.map ⟨false, True.intro⟩ =
    ⟨true, True.intro, True.intro⟩ := rfl

end Dominance

section Coverage

variable {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    (p : Problem X V) (f : Y → X) (coverage : FeasibleSurjection p f)
    (constraint : Y → Prop)
    (admissible : ∀ point : FeasiblePoint p, constraint (coverage.preimage point))

example (point : FeasiblePoint (p.pullback f)) :
    f ((coverage.restrictionImprovement constraint admissible).map point).1 = f point.1 :=
  coverage.restrictionImprovement_map_source constraint admissible point

example (point : FeasiblePoint (p.pullback f)) :
    ((p.pullback f).addConstraint constraint).objective
      ((coverage.restrictionImprovement constraint admissible).map point).1 =
      (p.pullback f).objective point.1 :=
  coverage.restrictionImprovement_objective_eq constraint admissible point

example : GlobalEquiv p ((p.pullback f).addConstraint constraint) :=
  (pullbackEquiv p f coverage).trans
    (restrictionEquiv _ _ (coverage.restrictionImprovement constraint admissible))

private def branchSource : Problem Nat Nat where
  objective := id
  feasible _ := True

private def trueBranch : FeasibleSurjection branchSource (Prod.fst : Nat × Bool → Nat) where
  preimage point := (point.1, true)
  rightInverse _ := rfl

private def branchRepair :=
  trueBranch.restrictionImprovement (fun point => point.2 = true) (fun _ => rfl)

-- Noninjective coverage selects one representative without imposing a branch
-- on the ordinary pullback. Its original objective and first coordinate survive.
example : (branchSource.pullback Prod.fst).feasible (3, false) := True.intro

example : ¬((branchSource.pullback Prod.fst).addConstraint
    (fun point => point.2 = true)).feasible (3, false) := by
  exact fun h => Bool.false_ne_true h.2

example : (branchRepair.map ⟨(3, false), True.intro⟩).1 = (3, true) := rfl

example : (branchSource.pullback Prod.fst).objective
    (branchRepair.map ⟨(3, false), True.intro⟩).1 = 3 := rfl

end Coverage

section RetainedCoordinates

variable {Retained : Type u} {New : Type v} {Old : Type w}
    {X : Type x} {Y : Type y} {V : Type z} [Preorder V]
    {f : Retained → New → Old} (rule : CoordinateParameterization f)
    (p : Problem X V) (sourceSplit : X ≃ Retained × Old) (targetSplit : Y ≃ Retained × New)
    (rangeCovered : ∀ point, p.feasible point →
      rule.range (sourceSplit point).1 (sourceSplit point).2)
    (constraint : Y → Prop)
    (admissible : ∀ point : FeasiblePoint p,
      constraint ((rule.toFeasibleSurjection p sourceSplit targetSplit rangeCovered).preimage point))

example (point : FeasiblePoint
    (p.pullback (CoordinateParameterization.coordinateMap f sourceSplit targetSplit))) :
    (targetSplit ((FeasibleSurjection.restrictionImprovement
      (rule.toFeasibleSurjection p sourceSplit targetSplit rangeCovered)
      constraint admissible).map point).1).1 =
      (targetSplit point.1).1 := by
  change (targetSplit ((rule.toFeasibleSurjection p sourceSplit targetSplit rangeCovered).preimage
    ⟨CoordinateParameterization.coordinateMap f sourceSplit targetSplit point.1, point.2⟩)).1 = _
  rw [rule.toFeasibleSurjection_preimage_retained]
  exact CoordinateParameterization.coordinateMap_retained f sourceSplit targetSplit point.1

end RetainedCoordinates

end MorewTest.Restriction
