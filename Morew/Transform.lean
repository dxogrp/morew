/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Syntax

/-!
# Verified primitive transformations

Problem transformations and their global equivalence proofs, used by the
`reformulation` command.
-/

namespace Morew

universe u v w z

/-- Decompose feasibility into a selected constraint and the retained constraints. -/
structure ConstraintDecomposition {X : Type u} {V : Type v}
    (p : Problem X V) (source : X → Prop) where
  /-- The part of the feasible predicate left unchanged by the transformation. -/
  remainder : X → Prop
  /-- The remainder and selected source constraint exactly recover the
  original feasible predicate. -/
  feasible_iff : ∀ x, p.feasible x ↔ remainder x ∧ source x

namespace Problem

/-- Append a constraint, preserving the decision space and objective.
For global equivalence, use `addConstraintEquiv` with an implication
from feasibility, or `restrictionEquiv` with a feasible improvement map. -/
def addConstraint {X : Type u} {V : Type v}
    (p : Problem X V) (constraint : X → Prop) : Problem X V where
  objective := p.objective
  feasible point := p.feasible point ∧ constraint point

@[simp]
theorem addConstraint_objective {X : Type u} {V : Type v}
    (p : Problem X V) (constraint : X → Prop) (point : X) :
    (p.addConstraint constraint).objective point = p.objective point := rfl

@[simp]
theorem addConstraint_feasible {X : Type u} {V : Type v}
    (p : Problem X V) (constraint : X → Prop) (point : X) :
    (p.addConstraint constraint).feasible point ↔
      p.feasible point ∧ constraint point := Iff.rfl

/-- Remove a selected constraint, preserving the decision space and objective.
`removeConstraintEquiv` proves equivalence when the retained constraints
imply the removed constraint. -/
def removeConstraint {X : Type u} {V : Type v}
    {selected : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p selected) : Problem X V where
  objective := p.objective
  feasible := decomposition.remainder

@[simp]
theorem removeConstraint_objective {X : Type u} {V : Type v}
    {selected : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p selected) (point : X) :
    (p.removeConstraint decomposition).objective point = p.objective point := rfl

@[simp]
theorem removeConstraint_feasible {X : Type u} {V : Type v}
    {selected : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p selected) (point : X) :
    (p.removeConstraint decomposition).feasible point ↔ decomposition.remainder point := Iff.rfl

/-- Replace a selected constraint by a predicate on the original and auxiliary
coordinates. `conditionalConstraintLiftEquivalence` proves equivalence under
the retained constraints. -/
def liftConstraintConditional {X : Type u} {V : Type v} {A : Type w}
    {source : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (target : X → A → Prop) : Problem (X × A) V where
  objective point := p.objective point.1
  feasible point := decomposition.remainder point.1 ∧ target point.1 point.2

@[simp]
theorem liftConstraintConditional_objective
    {X : Type u} {V : Type v} {A : Type w} {source : X → Prop}
    (p : Problem X V) (decomposition : ConstraintDecomposition p source)
    (target : X → A → Prop) (point : X × A) :
    (p.liftConstraintConditional decomposition target).objective point =
      p.objective point.1 := rfl

@[simp]
theorem liftConstraintConditional_feasible
    {X : Type u} {V : Type v} {A : Type w} {source : X → Prop}
    (p : Problem X V) (decomposition : ConstraintDecomposition p source)
    (target : X → A → Prop) (point : X × A) :
    (p.liftConstraintConditional decomposition target).feasible point ↔
      decomposition.remainder point.1 ∧ target point.1 point.2 := Iff.rfl

/-- Replace a selected constraint by an existentially equivalent predicate,
retaining the other constraints. -/
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

/-- Introduce an objective bound as a new optimization variable.

For an ordinary order this is an epigraph. For an `OrderDual` objective it is
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

/-- Introduce a hypograph bound `t ≤ f x` for maximization. The new variable
uses the underlying objective-value type. -/
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

/-- A right inverse on feasible source points for a change of variables. -/
structure FeasibleSurjection {X : Type u} {Y : Type v} {V : Type w}
    (p : Problem X V) (f : Y → X) where
  /-- Choose a transformed representative for each feasible source point. -/
  preimage : FeasiblePoint p → Y
  /-- The chosen representative maps back to the source point. -/
  rightInverse : ∀ x : FeasiblePoint p, f (preimage x) = x.1

/-- Pointwise-equal objectives and pointwise-equivalent feasible predicates
give a global equivalence via the identity map on decision points. -/
def pointwiseEquiv {X : Type u} {V : Type v} [Preorder V]
    (p q : Problem X V)
    (objective_eq : ∀ x, p.objective x = q.objective x)
    (feasible_iff : ∀ x, p.feasible x ↔ q.feasible x) :
    GlobalEquiv p q where
  forward := {
    map := fun x => ⟨x.1, (feasible_iff x.1).mp x.2⟩
    objective_le := fun x => le_of_eq (objective_eq x.1).symm }
  backward := {
    map := fun x => ⟨x.1, (feasible_iff x.1).mpr x.2⟩
    objective_le := fun x => le_of_eq (objective_eq x.1) }

/-- Add a consequence of current feasibility, preserving decision points and
objective values. -/
def addConstraintEquiv {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) (constraint : X → Prop)
    (implied : ∀ point, p.feasible point → constraint point) :
    GlobalEquiv p (p.addConstraint constraint) :=
  pointwiseEquiv p (p.addConstraint constraint) (fun _ => rfl)
    (fun point => ⟨fun feasible => ⟨feasible, implied point feasible⟩, And.left⟩)

/-- Remove a constraint implied by the retained constraints, preserving decision
points and objective values. -/
def removeConstraintEquiv {X : Type u} {V : Type v} [Preorder V]
    {selected : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p selected)
    (implied : ∀ point, decomposition.remainder point → selected point) :
    GlobalEquiv p (p.removeConstraint decomposition) :=
  pointwiseEquiv p (p.removeConstraint decomposition) (fun _ => rfl)
    (fun point => ⟨fun feasible => ((decomposition.feasible_iff point).mp feasible).1,
      fun retained => (decomposition.feasible_iff point).mpr ⟨retained, implied point retained⟩⟩)

/-- Restrict to an added constraint using a feasible improvement map.
The backward map is inclusion. -/
def restrictionEquiv {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) (constraint : X → Prop)
    (repair : GlobalImprovement p (p.addConstraint constraint)) :
    GlobalEquiv p (p.addConstraint constraint) where
  forward := repair
  backward := {
    map := fun point => ⟨point.1, point.2.1⟩
    objective_le := fun _ => le_rfl }

/-- Replacing a constraint by equivalent constraints with auxiliary variables
preserves global optimization. The forward map chooses feasible auxiliary
values; the backward map projects to the original coordinates. -/
noncomputable def conditionalConstraintLiftEquivalence
    {X : Type u} {V : Type v} {A : Type w} {source : X → Prop} [Preorder V]
    (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (target : X → A → Prop)
    (source_iff_exists : ∀ x, decomposition.remainder x →
      (source x ↔ ∃ a, target x a)) :
    GlobalEquiv p (p.liftConstraintConditional decomposition target) where
  forward := {
    map := fun x => by
      have hparts : decomposition.remainder x.1 ∧ source x.1 :=
        (decomposition.feasible_iff x.1).mp x.2
      have hexists : ∃ a, target x.1 a :=
        (source_iff_exists x.1 hparts.1).mp hparts.2
      exact ⟨(x.1, Classical.choose hexists), hparts.1,
        Classical.choose_spec hexists⟩
    objective_le := fun _ => le_rfl }
  backward := {
    map := fun point => by
      have hsource : source point.1.1 :=
        (source_iff_exists point.1.1 point.2.1).mpr ⟨point.1.2, point.2.2⟩
      exact ⟨point.1.1,
        (decomposition.feasible_iff point.1.1).mpr
          ⟨point.2.1, hsource⟩⟩
    objective_le := fun _ => le_rfl }

/-- Replacing a constraint by an existentially equivalent predicate preserves
global optimization. -/
noncomputable def exactConstraintLiftEquivalence
    {X : Type u} {V : Type v} {source : X → Prop} [Preorder V]
    (p : Problem X V)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ConstraintDecomposition p source) :
    GlobalEquiv p (p.liftConstraint lift decomposition) where
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
def pullbackEquiv {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    (p : Problem X V) (f : Y → X) (h : FeasibleSurjection p f) :
    GlobalEquiv p (p.pullback f) where
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

namespace FeasibleSurjection

/-- Choose an admissible preimage of each feasible source point, preserving
the represented point and its objective. -/
def restrictionImprovement
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {f : Y → X} (coverage : FeasibleSurjection p f)
    (constraint : Y → Prop)
    (admissible : ∀ point : FeasiblePoint p, constraint (coverage.preimage point)) :
    GlobalImprovement (p.pullback f) ((p.pullback f).addConstraint constraint) where
  map := fun point =>
    let source : FeasiblePoint p := ⟨f point.1, point.2⟩
    ⟨coverage.preimage source,
      by
        constructor
        · change p.feasible (f (coverage.preimage source))
          simpa only [coverage.rightInverse source] using source.2
        · exact admissible source⟩
  objective_le := fun point => by
    change p.objective (f (coverage.preimage ⟨f point.1, point.2⟩)) ≤
      p.objective (f point.1)
    exact le_of_eq (congrArg p.objective (coverage.rightInverse ⟨f point.1, point.2⟩))

/-- Selecting an admissible preimage preserves the represented source point. -/
theorem restrictionImprovement_map_source
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {f : Y → X} (coverage : FeasibleSurjection p f)
    (constraint : Y → Prop)
    (admissible : ∀ point : FeasiblePoint p, constraint (coverage.preimage point))
    (point : FeasiblePoint (p.pullback f)) :
    f ((coverage.restrictionImprovement constraint admissible).map point).1 =
      f point.1 :=
  coverage.rightInverse ⟨f point.1, point.2⟩

/-- Selecting an admissible preimage preserves the objective exactly, in either
the ordinary order or its dual. -/
theorem restrictionImprovement_objective_eq
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {f : Y → X} (coverage : FeasibleSurjection p f)
    (constraint : Y → Prop)
    (admissible : ∀ point : FeasiblePoint p, constraint (coverage.preimage point))
    (point : FeasiblePoint (p.pullback f)) :
    ((p.pullback f).addConstraint constraint).objective
      ((coverage.restrictionImprovement constraint admissible).map point).1 =
      (p.pullback f).objective point.1 :=
  congrArg p.objective (coverage.restrictionImprovement_map_source constraint admissible point)

end FeasibleSurjection

/-- The epigraph construction preserves global optimization behavior. -/
def epigraphEquiv {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) : GlobalEquiv p p.epigraph where
  forward := {
    map := fun x => ⟨(x.1, p.objective x.1), x.2, le_rfl⟩
    objective_le := fun _ => le_rfl }
  backward := {
    map := fun xt => ⟨xt.1.1, xt.2.1⟩
    objective_le := fun xt => xt.2.2 }

/-- The hypograph construction preserves global maximization behavior. -/
def hypographEquiv {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X (OrderDual V)) : GlobalEquiv p p.hypograph where
  forward := {
    map := fun x => ⟨(x.1, p.objective x.1), x.2, le_rfl⟩
    objective_le := fun _ => le_rfl }
  backward := {
    map := fun xt => ⟨xt.1.1, xt.2.1⟩
    objective_le := fun xt => xt.2.2 }

end Morew
