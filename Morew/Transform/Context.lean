/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform

/-!
# Epigraph and hypograph bounds for subexpressions

Replace a subexpression by an auxiliary bound while preserving global
optimization. The equivalence conditions use feasibility for objectives and
the remaining constraints for constraint substitutions.
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

/-- The inequality between the selected value and its auxiliary bound. -/
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

/-- Conditions for replacing `f x` in the objective `C x (f x)` by an auxiliary
bound. `A` orders the selected values; `V` carries the optimization order. -/
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

/-- Replace an objective subexpression by an auxiliary variable and add its
bound to the original constraints. -/
def objectiveBoundAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) (direction : BoundDirection) :
    Problem (X × A) V where
  objective point := C point.1 point.2
  feasible point := p.feasible point.1 ∧ direction.Rel (f point.1) point.2

/-- The transformed objective is `C x a`, where `a` is the auxiliary variable. -/
@[simp]
theorem objectiveBoundAt_objective {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) (direction : BoundDirection)
    (point : X × A) :
    (p.objectiveBoundAt f C direction).objective point = C point.1 point.2 := rfl

/-- Introducing an objective bound retains every original constraint. -/
@[simp]
theorem objectiveBoundAt_feasible {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) (direction : BoundDirection)
    (point : X × A) :
    (p.objectiveBoundAt f C direction).feasible point ↔
      p.feasible point.1 ∧ direction.Rel (f point.1) point.2 := Iff.rfl

/-- Introduce an upper bound on an objective subexpression. -/
def epigraphAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) : Problem (X × A) V :=
  p.objectiveBoundAt f C .upper

/-- Introduce a lower bound on an objective subexpression. -/
def hypographAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    (p : Problem X V) (f : X → A) (C : X → A → V) : Problem (X × A) V :=
  p.objectiveBoundAt f C .lower

end Problem

/-- The auxiliary objective bound gives a global equivalence under `context`. -/
def objectiveBoundAtEquiv {X : Type u} {A : Type v} {V : Type w}
    [Preorder A] [Preorder V] (p : Problem X V) (f : X → A) (C : X → A → V)
    (direction : BoundDirection) (context : ObjectiveBoundContext p f C direction) :
    GlobalEquiv p (p.objectiveBoundAt f C direction) where
  forward := {
    map := fun x => ⟨(x.1, f x.1), x.2, direction.rel_refl (f x.1)⟩
    objective_le := fun x => le_of_eq (context.atValue x.1) }
  backward := {
    map := fun point => ⟨point.1.1, point.2.1⟩
    objective_le := fun point =>
      context.backward point.1.1 point.2.1 point.1.2 point.2.2 }

/-- The epigraph substitution gives a global equivalence under `context`. -/
def objectiveEpigraphAtEquiv {X : Type u} {A : Type v} {V : Type w}
    [Preorder A] [Preorder V] (p : Problem X V) (f : X → A) (C : X → A → V)
    (context : ObjectiveEpigraphContext p f C) :
    GlobalEquiv p (p.epigraphAt f C) :=
  objectiveBoundAtEquiv p f C .upper context

/-- The hypograph substitution gives a global equivalence under `context`. -/
def objectiveHypographAtEquiv {X : Type u} {A : Type v} {V : Type w}
    [Preorder A] [Preorder V] (p : Problem X V) (f : X → A) (C : X → A → V)
    (context : ObjectiveHypographContext p f C) :
    GlobalEquiv p (p.hypographAt f C) :=
  objectiveBoundAtEquiv p f C .lower context

/-- Conditions for replacing a constraint subexpression by an auxiliary bound.
The new constraints must imply the original constraint. -/
structure ConstraintBoundContext {X : Type u} {A : Type v} [LE A]
    (remainder source : X → Prop) (f : X → A) (C : X → A → Prop)
    (direction : BoundDirection) where
  /-- Restoring the selected value gives the original selected predicate. -/
  atValue : ∀ x, source x ↔ C x (f x)
  /-- The new predicate and bound recover the original selected constraint. -/
  backward : ∀ x, remainder x → ∀ a,
    direction.Rel (f x) a → C x a → source x

namespace ConstraintBoundContext

/-- Express a bound on a subexpression as an existential constraint equivalence
under the retained assumptions. -/
def toConstraintRepr {X : Type u} {A : Type v} [Preorder A]
    {remainder source : X → Prop} {f : X → A} {C : X → A → Prop}
    {direction : BoundDirection}
    (context : ConstraintBoundContext remainder source f C direction) :
    ConstraintRepr (fun x => remainder x ∧ source x) where
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

/-- Replace a subexpression in a constraint by an auxiliary bound, preserving
the objective and retained constraints. -/
def constraintBoundAt {X : Type u} {A : Type v} {V : Type w} [LE A]
    {source : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (f : X → A) (C : X → A → Prop) (direction : BoundDirection) :
    Problem (X × A) V where
  objective point := p.objective point.1
  feasible point := decomposition.remainder point.1 ∧ C point.1 point.2 ∧
    direction.Rel (f point.1) point.2

/-- Introducing a bound in a constraint preserves the objective. -/
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

/-- Introducing a bound in a constraint preserves global optimization in either sense. -/
noncomputable def constraintBoundAtEquiv
    {X : Type u} {A : Type v} {V : Type w} [Preorder A] [Preorder V]
    {source : X → Prop} (p : Problem X V)
    (decomposition : ConstraintDecomposition p source)
    (f : X → A) (C : X → A → Prop) (direction : BoundDirection)
    (context : ConstraintBoundContext decomposition.remainder source f C direction) :
    GlobalEquiv p (p.constraintBoundAt decomposition f C direction) := by
  let full : ConstraintDecomposition p (fun x => decomposition.remainder x ∧ source x) := {
    remainder := fun _ => True
    feasible_iff := fun x => by simpa only [true_and] using decomposition.feasible_iff x }
  let repr := context.toConstraintRepr
  exact (replaceConstraintEquiv p repr full).trans
    (pointwiseEquiv (p.replaceConstraint repr full)
      (p.constraintBoundAt (A := A) decomposition f C direction)
      (fun _ => rfl) (fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩))

end Morew
