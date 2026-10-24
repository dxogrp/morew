/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform

/-!
# Bounds at selected objective and constraint occurrences

An occurrence context retains the original selected value and the function or
predicate obtained by replacing just that occurrence. Its certificate proves
the direction needed to recover a source feasible point. Objective contexts may
use source feasibility; constraint contexts may use only the retained rows.
-/

namespace Morew

universe u v w

/-- Whether an auxiliary value bounds the selected value above or below. -/
inductive BoundDirection where
  /-- The selected value is at most the auxiliary value. -/
  | upper
  /-- The auxiliary value is at most the selected value. -/
  | lower
  deriving Inhabited, BEq, Repr

namespace BoundDirection

/-- The order relation imposed by an occurrence-bound step. -/
def Rel {A : Type u} [LE A] (direction : BoundDirection) (value auxiliary : A) : Prop :=
  match direction with
  | .upper => value ≤ auxiliary
  | .lower => auxiliary ≤ value

/-- An upper bound uses the ordinary order of the selected value. -/
@[simp]
theorem upper_rel {A : Type u} [LE A] (value auxiliary : A) :
    upper.Rel value auxiliary ↔ value ≤ auxiliary := Iff.rfl

/-- A lower bound reverses the two arguments of the ordinary order. -/
@[simp]
theorem lower_rel {A : Type u} [LE A] (value auxiliary : A) :
    lower.Rel value auxiliary ↔ auxiliary ≤ value := Iff.rfl

/-- Choosing the original value always satisfies its auxiliary bound. -/
theorem rel_refl {A : Type u} [Preorder A] (direction : BoundDirection) (value : A) :
    direction.Rel value value := by
  cases direction <;> exact le_rfl

end BoundDirection

/-- A certificate for replacing one objective occurrence by an auxiliary bound.

`V` carries the optimization order, including `OrderDual` for maximization.
The selected value's ordered type `A` need not be the objective-value type.
The parameters retain the complete selected function and extracted context. -/
structure ObjectiveBoundContext {X : Type u} {A : Type v} {V : Type w}
    [LE A] [LE V] (p : Problem X V) (f : X → A) (C : X → A → V)
    (direction : BoundDirection) where
  /-- Restoring the selected value gives exactly the original objective. -/
  atValue : ∀ x, C x (f x) = p.objective x
  /-- Projection to a source feasible point does not worsen its objective. -/
  backward : ∀ x, p.feasible x → ∀ a,
    direction.Rel (f x) a → p.objective x ≤ C x a

/-- An objective context certified for an upper bound on its selected value. -/
abbrev ObjectiveEpigraphContext {X : Type u} {A : Type v} {V : Type w}
    [LE A] [LE V] (p : Problem X V) (f : X → A) (C : X → A → V) :=
  ObjectiveBoundContext p f C .upper

/-- An objective context certified for a lower bound on its selected value. -/
abbrev ObjectiveHypographContext {X : Type u} {A : Type v} {V : Type w}
    [LE A] [LE V] (p : Problem X V) (f : X → A) (C : X → A → V) :=
  ObjectiveBoundContext p f C .lower

namespace Problem

/-- Replace the selected objective occurrence by an auxiliary value and retain
the original feasible predicate together with the selected bound. -/
def objectiveBoundAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) (direction : BoundDirection) :
    Problem (X × A) V where
  objective point := C point.1 point.2
  feasible point := p.feasible point.1 ∧ direction.Rel (f point.1) point.2

/-- The transformed objective evaluates the extracted occurrence context. -/
@[simp]
theorem objectiveBoundAt_objective {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) (direction : BoundDirection)
    (point : X × A) :
    (p.objectiveBoundAt f C direction).objective point = C point.1 point.2 := rfl

/-- An objective occurrence lift retains every original constraint. -/
@[simp]
theorem objectiveBoundAt_feasible {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) (direction : BoundDirection)
    (point : X × A) :
    (p.objectiveBoundAt f C direction).feasible point ↔
      p.feasible point.1 ∧ direction.Rel (f point.1) point.2 := Iff.rfl

/-- Introduce an upper bound at a selected objective occurrence. -/
def epigraphAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) : Problem (X × A) V :=
  p.objectiveBoundAt f C .upper

/-- Introduce a lower bound at a selected objective occurrence. -/
def hypographAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) : Problem (X × A) V :=
  p.objectiveBoundAt f C .lower

end Problem

/-- A certified objective occurrence bound preserves global optimization. -/
def objectiveBoundAtEquivalence {X : Type u} {A : Type v} {V : Type w}
    [Preorder A] [Preorder V] (p : Problem X V) (f : X → A) (C : X → A → V)
    (direction : BoundDirection) (context : ObjectiveBoundContext p f C direction) :
    GlobalEquivalence p (p.objectiveBoundAt f C direction) where
  forward := {
    map := fun x => ⟨(x.1, f x.1), x.2, direction.rel_refl (f x.1)⟩
    objective_le := fun x => le_of_eq (context.atValue x.1) }
  backward := {
    map := fun point => ⟨point.1.1, point.2.1⟩
    objective_le := fun point =>
      context.backward point.1.1 point.2.1 point.1.2 point.2.2 }

/-- The upper-bound specialization of objective occurrence equivalence. -/
def objectiveEpigraphAtEquivalence {X : Type u} {A : Type v} {V : Type w}
    [Preorder A] [Preorder V] (p : Problem X V) (f : X → A) (C : X → A → V)
    (context : ObjectiveEpigraphContext p f C) :
    GlobalEquivalence p (p.epigraphAt f C) :=
  objectiveBoundAtEquivalence p f C .upper context

/-- The lower-bound specialization of objective occurrence equivalence. -/
def objectiveHypographAtEquivalence {X : Type u} {A : Type v} {V : Type w}
    [Preorder A] [Preorder V] (p : Problem X V) (f : X → A) (C : X → A → V)
    (context : ObjectiveHypographContext p f C) :
    GlobalEquivalence p (p.hypographAt f C) :=
  objectiveBoundAtEquivalence p f C .lower context

/-- A certificate for replacing one occurrence in a selected constraint.

Recovery may use the retained constraints, but never assume the selected source
constraint. This prevents circular proofs of exactness. -/
structure ConstraintBoundContext {X : Type u} {A : Type v} [LE A]
    (remainder source : X → Prop) (f : X → A) (C : X → A → Prop)
    (direction : BoundDirection) where
  /-- Restoring the selected value gives the original selected predicate. -/
  atValue : ∀ x, source x ↔ C x (f x)
  /-- The new predicate and bound recover the original selected constraint. -/
  backward : ∀ x, remainder x → ∀ a,
    direction.Rel (f x) a → C x a → source x

namespace ConstraintBoundContext

/-- Convert a contextual occurrence certificate to the existing exact-lift
interface by retaining the assumptions on both sides of the equivalence. -/
def toExactConstraintLift {X : Type u} {A : Type v} [Preorder A]
    {remainder source : X → Prop} {f : X → A} {C : X → A → Prop}
    {direction : BoundDirection}
    (context : ConstraintBoundContext remainder source f C direction) :
    ExactConstraintLift (fun x => remainder x ∧ source x) where
  Auxiliary := A
  target x a := remainder x ∧ C x a ∧ direction.Rel (f x) a
  source_iff_exists x := by
    constructor
    · rintro ⟨hr, hs⟩
      exact ⟨f x, hr, (context.atValue x).mp hs, direction.rel_refl (f x)⟩
    · rintro ⟨a, hr, hc, ha⟩
      exact ⟨hr, context.backward x hr a ha hc⟩

end ConstraintBoundContext

namespace Problem

/-- Replace one occurrence of one selected constraint, leaving the objective
and every retained row unchanged. The source label's predicate becomes `C`. -/
def constraintBoundAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    {source : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (f : X → A) (C : X → A → Prop) (direction : BoundDirection) :
    Problem (X × A) V where
  objective point := p.objective point.1
  feasible point := decomposition.remainder point.1 ∧ C point.1 point.2 ∧
    direction.Rel (f point.1) point.2

/-- Constraint occurrence lifting preserves the original objective exactly. -/
@[simp]
theorem constraintBoundAt_objective {X : Type u} {A : Type v} {V : Type w} [LE A]
    {source : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (f : X → A) (C : X → A → Prop) (direction : BoundDirection) (point : X × A) :
    (p.constraintBoundAt decomposition f C direction).objective point =
      p.objective point.1 := rfl

/-- The selected predicate and its auxiliary bound are both required. -/
@[simp]
theorem constraintBoundAt_feasible {X : Type u} {A : Type v} {V : Type w} [LE A]
    {source : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (f : X → A) (C : X → A → Prop) (direction : BoundDirection) (point : X × A) :
    (p.constraintBoundAt decomposition f C direction).feasible point ↔
      decomposition.remainder point.1 ∧ C point.1 point.2 ∧
        direction.Rel (f point.1) point.2 := Iff.rfl

end Problem

/-- Constraint occurrence bounds preserve global optimization in either sense.
The construction factors through the existing exact-constraint-lift theorem. -/
noncomputable def constraintBoundAtEquivalence
    {X : Type u} {A : Type v} {V : Type w} [Preorder A] [Preorder V]
    {source : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (f : X → A) (C : X → A → Prop) (direction : BoundDirection)
    (context : ConstraintBoundContext decomposition.remainder source f C direction) :
    GlobalEquivalence p (p.constraintBoundAt decomposition f C direction) := by
  let full : ConstraintDecomposition p (fun x => decomposition.remainder x ∧ source x) := {
    remainder := fun _ => True
    feasible_iff := fun x => by simpa only [true_and] using decomposition.feasible_iff x }
  let lift := context.toExactConstraintLift
  exact (exactConstraintLiftEquivalence p lift full).trans
    (pointwiseEquivalence (p.liftConstraint lift full)
      (p.constraintBoundAt (A := A) decomposition f C direction)
      (fun _ => rfl) (fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩))

end Morew
