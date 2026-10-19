import PTran.Syntax

/-!
# Verified primitive transformations

This module contains the semantic building blocks used by the surface
`reformulation` command.  None of these definitions assumes convexity.
-/

namespace PTran

universe u v w z

/-- An exact replacement of a predicate by a predicate over auxiliary
variables.

The existential equivalence is the soundness boundary: a one-way implication
would describe a relaxation rather than an equivalent transformation.  No
uniqueness or constructive choice of the auxiliary value is required. -/
structure ExactConstraintLift {X : Type u} (source : X → Prop) where
  /-- The type of auxiliary values introduced by the replacement. -/
  Auxiliary : Type v
  /-- The replacement predicate over an original point and an auxiliary
  value. -/
  target : X → Auxiliary → Prop
  /-- The replacement is feasible for some auxiliary value exactly when the
  source predicate holds. -/
  source_iff_exists : ∀ x, source x ↔ ∃ a, target x a

namespace ExactConstraintLift

/-- Regard a pointwise propositional equivalence as an exact lift with no
semantic auxiliary data.  `Unit` represents the absence of auxiliary
variables. -/
def ofIff {X : Type u} {source : X → Prop} (replacement : X → Prop)
    (h : ∀ x, source x ↔ replacement x) :
    ExactConstraintLift source where
  Auxiliary := Unit
  target x _ := replacement x
  source_iff_exists x := by
    constructor
    · intro hx
      exact ⟨(), (h x).mp hx⟩
    · rintro ⟨_, hx⟩
      exact (h x).mpr hx

end ExactConstraintLift

/-- An exact auxiliary-variable representation of the graph equation
`y = f x`.

The existential equivalence, rather than either implication alone, ensures
that using the representation preserves feasibility. -/
structure GraphRepresentation {X : Type u} {Y : Type v} (f : X → Y) where
  /-- The type of auxiliary values used by the representation. -/
  Auxiliary : Type w
  /-- The represented graph predicate. -/
  target : X → Y → Auxiliary → Prop
  /-- The represented predicate is existentially equivalent to the graph
  equation. -/
  source_iff_exists : ∀ x y, y = f x ↔ ∃ a, target x y a

namespace GraphRepresentation

/-- Instantiate a graph representation inside an arbitrary decision domain. -/
def toExactConstraintLift {X : Type u} {Y : Type v} {Z : Type z} {f : X → Y}
    (representation : GraphRepresentation.{u, v, w} f)
    (input : Z → X) (output : Z → Y) :
    ExactConstraintLift (fun point => output point = f (input point)) where
  Auxiliary := representation.Auxiliary
  target point := representation.target (input point) (output point)
  source_iff_exists point :=
    representation.source_iff_exists (input point) (output point)

/-- Instantiate a graph representation for the symmetric equation
`f x = y` inside an arbitrary decision domain. -/
def toExactConstraintLiftSymm
    {X : Type u} {Y : Type v} {Z : Type z} {f : X → Y}
    (representation : GraphRepresentation.{u, v, w} f)
    (input : Z → X) (output : Z → Y) :
    ExactConstraintLift (fun point => f (input point) = output point) where
  Auxiliary := representation.Auxiliary
  target point := representation.target (input point) (output point)
  source_iff_exists point := by
    constructor
    · intro h
      exact (representation.source_iff_exists _ _).mp h.symm
    · intro h
      exact ((representation.source_iff_exists _ _).mpr h).symm

end GraphRepresentation

/-- An exact auxiliary-variable representation of an epigraph predicate
`f x ≤ t`.

Only an `LE` relation is needed: exactness is supplied explicitly by the
existential equivalence. -/
structure EpigraphRepresentation {X : Type u} {Y : Type v} [LE Y]
    (f : X → Y) where
  /-- The type of auxiliary values used by the representation. -/
  Auxiliary : Type w
  /-- The represented epigraph predicate. -/
  target : X → Y → Auxiliary → Prop
  /-- The represented predicate is existentially equivalent to membership in
  the epigraph. -/
  source_iff_exists : ∀ x t, f x ≤ t ↔ ∃ a, target x t a

namespace EpigraphRepresentation

/-- Instantiate an epigraph representation inside an arbitrary decision
domain. -/
def toExactConstraintLift
    {X : Type u} {Y : Type v} {Z : Type z} [LE Y] {f : X → Y}
    (representation : EpigraphRepresentation.{u, v, w} f)
    (input : Z → X) (bound : Z → Y) :
    ExactConstraintLift (fun point => f (input point) ≤ bound point) where
  Auxiliary := representation.Auxiliary
  target point := representation.target (input point) (bound point)
  source_iff_exists point :=
    representation.source_iff_exists (input point) (bound point)

end EpigraphRepresentation

/-- An exact auxiliary-variable representation of a hypograph predicate
`t ≤ f x`.

Only an `LE` relation is needed: exactness is supplied explicitly by the
existential equivalence. -/
structure HypographRepresentation {X : Type u} {Y : Type v} [LE Y]
    (f : X → Y) where
  /-- The type of auxiliary values used by the representation. -/
  Auxiliary : Type w
  /-- The represented hypograph predicate. -/
  target : X → Y → Auxiliary → Prop
  /-- The represented predicate is existentially equivalent to membership in
  the hypograph. -/
  source_iff_exists : ∀ x t, t ≤ f x ↔ ∃ a, target x t a

namespace HypographRepresentation

/-- Instantiate a hypograph representation inside an arbitrary decision
domain. -/
def toExactConstraintLift
    {X : Type u} {Y : Type v} {Z : Type z} [LE Y] {f : X → Y}
    (representation : HypographRepresentation.{u, v, w} f)
    (input : Z → X) (bound : Z → Y) :
    ExactConstraintLift (fun point => bound point ≤ f (input point)) where
  Auxiliary := representation.Auxiliary
  target point := representation.target (input point) (bound point)
  source_iff_exists point :=
    representation.source_iff_exists (input point) (bound point)

end HypographRepresentation

namespace Problem

set_option linter.unusedVariables.funArgs false in
/-- Replace one factor of a problem's feasible predicate by an exact
auxiliary-variable lift.

The decomposition identifies the selected source predicate while leaving all
other feasibility conditions in `remainder`.  Presentation details such as
constraint labels are intentionally absent from this semantic constructor. -/
@[nolint unusedArguments]
def liftConstraint {X : Type u} {V : Type v} {source : X → Prop}
    (p : Problem X V) (remainder : X → Prop)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ∀ x, p.feasible x ↔ remainder x ∧ source x) :
    Problem (X × lift.Auxiliary) V where
  objective point := p.objective point.1
  feasible point := remainder point.1 ∧ lift.target point.1 point.2

@[simp]
theorem liftConstraint_objective
    {X : Type u} {V : Type v} {source : X → Prop}
    (p : Problem X V) (remainder : X → Prop)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ∀ x, p.feasible x ↔ remainder x ∧ source x)
    (point : X × lift.Auxiliary) :
    (p.liftConstraint remainder lift decomposition).objective point =
      p.objective point.1 := rfl

@[simp]
theorem liftConstraint_feasible
    {X : Type u} {V : Type v} {source : X → Prop}
    (p : Problem X V) (remainder : X → Prop)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ∀ x, p.feasible x ↔ remainder x ∧ source x)
    (point : X × lift.Auxiliary) :
    (p.liftConstraint remainder lift decomposition).feasible point ↔
      remainder point.1 ∧ lift.target point.1 point.2 := Iff.rfl

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
    (p : Problem X V) (remainder : X → Prop)
    (lift : ExactConstraintLift.{u, w} source)
    (decomposition : ∀ x, p.feasible x ↔ remainder x ∧ source x) :
    GlobalEquivalence p (p.liftConstraint remainder lift decomposition) where
  forward := {
    map := fun x => by
      have hparts : remainder x.1 ∧ source x.1 :=
        (decomposition x.1).mp x.2
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
        (decomposition point.1.1).mpr ⟨point.2.1, hsource⟩⟩
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

end PTran
