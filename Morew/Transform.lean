/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Syntax

/-!
# Verified primitive transformations

This module contains the semantic building blocks used by the surface
`reformulation` command.  None of these definitions assumes convexity.
-/

namespace Morew

universe u v w z

/-- An exact decomposition of a problem's feasible predicate into the source
constraint selected for replacement and the remainder left unchanged. -/
structure ConstraintDecomposition {X : Type u} {V : Type v}
    (p : Problem X V) (source : X → Prop) where
  /-- The part of the feasible predicate left unchanged by the lift. -/
  remainder : X → Prop
  /-- The remainder and selected source constraint exactly recover the
  original feasible predicate. -/
  feasible_iff : ∀ x, p.feasible x ↔ remainder x ∧ source x

namespace Problem

/-- Replace one factor of a problem's feasible predicate by an exact
auxiliary-variable lift.

The decomposition identifies the selected source predicate while leaving all
other feasibility conditions in `remainder`.  Presentation details such as
constraint labels are intentionally absent from this semantic constructor. -/
def liftConstraint {X : Type u} {V : Type v} {source : X → Prop}
    (p : Problem X V)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ConstraintDecomposition p source) :
    Problem (X × lift.Auxiliary) V where
  objective point := p.objective point.1
  feasible point :=
    decomposition.remainder point.1 ∧ lift.target point.1 point.2

@[simp]
theorem liftConstraint_objective
    {X : Type u} {V : Type v} {source : X → Prop}
    (p : Problem X V)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ConstraintDecomposition p source)
    (point : X × lift.Auxiliary) :
    (p.liftConstraint lift decomposition).objective point =
      p.objective point.1 := rfl

@[simp]
theorem liftConstraint_feasible
    {X : Type u} {V : Type v} {source : X → Prop}
    (p : Problem X V)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ConstraintDecomposition p source)
    (point : X × lift.Auxiliary) :
    (p.liftConstraint lift decomposition).feasible point ↔
      decomposition.remainder point.1 ∧
        lift.target point.1 point.2 := Iff.rfl

/-- Pull an optimization problem back along a map of decision spaces. -/
def pullback {X : Type u} {Y : Type v} {V : Type w}
    (p : Problem X V) (f : Y → X) : Problem Y V where
  objective y := p.objective (f y)
  feasible y := p.feasible (f y)

@[simp]
theorem pullback_objective {X : Type u} {Y : Type v} {V : Type w}
    (p : Problem X V) (f : Y → X) (y : Y) :
    (p.pullback f).objective y = p.objective (f y) := rfl

@[simp]
theorem pullback_feasible {X : Type u} {Y : Type v} {V : Type w}
    (p : Problem X V) (f : Y → X) (y : Y) :
    (p.pullback f).feasible y ↔ p.feasible (f y) := Iff.rfl

/-- Introduce an objective bound as a new decision variable.

For an ordinary order this is an epigraph.  For an `OrderDual` objective it is
the corresponding hypograph in the underlying order. -/
def epigraph {X : Type u} {V : Type v} [LE V]
    (p : Problem X V) : Problem (X × V) V where
  objective xt := xt.2
  feasible xt := p.feasible xt.1 ∧ p.objective xt.1 ≤ xt.2

@[simp]
theorem epigraph_objective {X : Type u} {V : Type v} [LE V]
    (p : Problem X V) (xt : X × V) :
    p.epigraph.objective xt = xt.2 := rfl

@[simp]
theorem epigraph_feasible {X : Type u} {V : Type v} [LE V]
    (p : Problem X V) (xt : X × V) :
    p.epigraph.feasible xt ↔
      p.feasible xt.1 ∧ p.objective xt.1 ≤ xt.2 := Iff.rfl

/-- Introduce an objective bound for a maximization problem represented over
the dual order.  The new variable is kept in the underlying value type so the
surface constraint has its natural orientation `t ≤ f x`. -/
def hypograph {X : Type u} {V : Type v} [LE V]
    (p : Problem X (OrderDual V)) : Problem (X × V) (OrderDual V) where
  objective xt := xt.2
  feasible xt := p.feasible xt.1 ∧ xt.2 ≤ (p.objective xt.1 : V)

@[simp]
theorem hypograph_objective {X : Type u} {V : Type v} [LE V]
    (p : Problem X (OrderDual V)) (xt : X × V) :
    p.hypograph.objective xt = xt.2 := rfl

@[simp]
theorem hypograph_feasible {X : Type u} {V : Type v} [LE V]
    (p : Problem X (OrderDual V)) (xt : X × V) :
    p.hypograph.feasible xt ↔
      p.feasible xt.1 ∧ xt.2 ≤ (p.objective xt.1 : V) := Iff.rfl

end Problem

/-- Evidence that a change of variables covers every feasible source point.

Only a right inverse on feasible points is required.  In particular, the map
need not be injective or globally surjective. -/
structure FeasibleSurjection {X : Type u} {Y : Type v} {V : Type w}
    (p : Problem X V) (f : Y → X) where
  /-- Choose a transformed representative for each feasible source point. -/
  preimage : FeasiblePoint p → Y
  /-- The chosen representative maps back to the source point. -/
  rightInverse : ∀ x : FeasiblePoint p, f (preimage x) = x.1

/-- Pointwise-equal objectives and pointwise-equivalent feasible predicates
give a global equivalence via the identity map on decision points.

The surface reformulation engine uses this primitive to turn expression and
constraint simplification into a checked certificate rather than merely
changing presentation metadata. -/
def pointwiseEquivalence {X : Type u} {V : Type v} [Preorder V]
    (p q : Problem X V)
    (objective_eq : ∀ x, p.objective x = q.objective x)
    (feasible_iff : ∀ x, p.feasible x ↔ q.feasible x) :
    GlobalEquivalence p q where
  forward := {
    map := fun x => ⟨x.1, (feasible_iff x.1).mp x.2⟩
    objective_le := fun x => le_of_eq (objective_eq x.1).symm }
  backward := {
    map := fun x => ⟨x.1, (feasible_iff x.1).mpr x.2⟩
    objective_le := fun x => le_of_eq (objective_eq x.1) }

/-- Replacing a constraint by an existentially equivalent auxiliary-variable
predicate preserves global optimization behavior.

The forward map uses classical choice only to select an auxiliary witness.
The certificate does not require that witness to be unique or computable. -/
noncomputable def exactConstraintLiftEquivalence
    {X : Type u} {V : Type v} {source : X → Prop} [Preorder V]
    (p : Problem X V)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ConstraintDecomposition p source) :
    GlobalEquivalence p (p.liftConstraint lift decomposition) where
  forward := {
    map := fun x => by
      have hparts : decomposition.remainder x.1 ∧ source x.1 :=
        (decomposition.feasible_iff x.1).mp x.2
      have hexists : ∃ a, lift.target x.1 a :=
        (lift.source_iff_exists x.1).mp hparts.2
      exact ⟨(x.1, Classical.choose hexists), hparts.1,
        Classical.choose_spec hexists⟩
    objective_le := fun _ => le_rfl }
  backward := {
    map := fun point => by
      have hsource : source point.1.1 :=
        (lift.source_iff_exists point.1.1).mpr ⟨point.1.2, point.2.2⟩
      exact ⟨point.1.1,
        (decomposition.feasible_iff point.1.1).mpr
          ⟨point.2.1, hsource⟩⟩
    objective_le := fun _ => le_rfl }

/-- Pullback along a feasibly surjective map is a global equivalence. -/
def pullbackEquivalence {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    (p : Problem X V) (f : Y → X) (h : FeasibleSurjection p f) :
    GlobalEquivalence p (p.pullback f) where
  forward := {
    map := fun x =>
      ⟨h.preimage x, by
        change p.feasible (f (h.preimage x))
        simpa only [h.rightInverse x] using x.2⟩
    objective_le := fun x => by
      change p.objective (f (h.preimage x)) ≤ p.objective x.1
      simpa only [h.rightInverse x] using (le_refl (p.objective x.1)) }
  backward := {
    map := fun y => ⟨f y.1, y.2⟩
    objective_le := fun _ => le_rfl }

/-- The epigraph construction preserves global optimization behavior. -/
def epigraphEquivalence {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) : GlobalEquivalence p p.epigraph where
  forward := {
    map := fun x => ⟨(x.1, p.objective x.1), x.2, le_rfl⟩
    objective_le := fun _ => le_rfl }
  backward := {
    map := fun xt => ⟨xt.1.1, xt.2.1⟩
    objective_le := fun xt => xt.2.2 }

/-- The hypograph construction preserves global maximization behavior. -/
def hypographEquivalence {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X (OrderDual V)) : GlobalEquivalence p p.hypograph where
  forward := {
    map := fun x => ⟨(x.1, p.objective x.1), x.2, le_rfl⟩
    objective_le := fun _ => le_rfl }
  backward := {
    map := fun xt => ⟨xt.1.1, xt.2.1⟩
    objective_le := fun xt => xt.2.2 }

end Morew
