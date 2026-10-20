import Mathlib.Order.OrderDual

/-!
# Semantic core for PTran

This module defines optimization problems and the certificates used to compare
them.  The definitions deliberately make no convexity assumptions.  They also
do not require the maps in a global equivalence to be inverses: a map in each
direction, together with the corresponding objective inequalities, is enough
to preserve global optimization behavior.
-/

namespace PTran

universe u v w

/-- Whether an optimization problem is minimized or maximized.

Maximization is represented semantically by `OrderDual`; this explicit sense
is shared by certified target data and presentation metadata. -/
inductive ObjectiveSense where
  /-- Minimize the objective in its ordinary order. -/
  | minimize
  /-- Maximize the objective in its ordinary order. -/
  | maximize
  deriving Inhabited, BEq, Repr

/-- An optimization problem before choosing whether its order is read as a
minimization or maximization order.

Maximization is represented by taking `V` to be `OrderDual W`.  Constraint
names and other presentation information are intentionally kept outside this
semantic structure. -/
structure Problem (X : Type u) (V : Type v) where
  /-- The objective value at a decision point. -/
  objective : X → V
  /-- The conjunction of the problem's constraints. -/
  feasible : X → Prop

/-- A decision point together with evidence that it is feasible. -/
abbrev FeasiblePoint {X : Type u} {V : Type v} (p : Problem X V) :=
  {x : X // p.feasible x}

namespace Problem

/-- View the order on a problem's objective values in the opposite direction.
In particular, a maximization problem with values in `V` is represented as a
problem with values in `OrderDual V`. -/
def orderDual {X : Type u} {V : Type v} (p : Problem X V) :
    Problem X (OrderDual V) where
  objective := p.objective
  feasible := p.feasible

@[simp]
theorem orderDual_objective {X : Type u} {V : Type v} (p : Problem X V)
    (x : X) : p.orderDual.objective x = p.objective x := rfl

@[simp]
theorem orderDual_feasible {X : Type u} {V : Type v} (p : Problem X V)
    (x : X) : p.orderDual.feasible x ↔ p.feasible x := Iff.rfl

@[simp]
theorem orderDual_orderDual {X : Type u} {V : Type v} (p : Problem X V) :
    p.orderDual.orderDual = p := by
  cases p
  rfl

/-- The problem has at least one feasible decision point. -/
def HasFeasiblePoint {X : Type u} {V : Type v} (p : Problem X V) : Prop :=
  Nonempty (FeasiblePoint p)

/-- A feasible point is globally optimal for the order carried by `V`.

For ordinary ordered values this is global minimality.  For values in
`OrderDual V` it is global maximality in the original order. -/
def IsGlobalOptimum {X : Type u} {V : Type v} [LE V]
    (p : Problem X V) (x : FeasiblePoint p) : Prop :=
  ∀ y : FeasiblePoint p, p.objective x.1 ≤ p.objective y.1

/-- The problem attains a global optimum. -/
def HasGlobalOptimum {X : Type u} {V : Type v} [LE V]
    (p : Problem X V) : Prop :=
  ∃ x : FeasiblePoint p, p.IsGlobalOptimum x

/-- `b` is a lower bound on all feasible objective values.  For an objective
in an order dual this is an upper bound in the original order. -/
def IsObjectiveLowerBound {X : Type u} {V : Type v} [LE V]
    (p : Problem X V) (b : V) : Prop :=
  ∀ x : FeasiblePoint p, b ≤ p.objective x.1

/-- There is a feasible objective value strictly below every proposed bound.
For an objective in an order dual this is unboundedness above in the original
order.  The strict inequality is essential on orders with a least element: a
problem attaining that element is bounded, not unbounded. -/
def IsUnbounded {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) : Prop :=
  ∀ b : V, ∃ x : FeasiblePoint p, p.objective x.1 < b

end Problem

/-- A one-way certificate from `p` to `q`.

Every feasible point of `p` is sent to a feasible point of `q` whose objective
is no worse in the minimization order.  This relation is the semantic seed for
both reformulations and future relaxations. -/
structure GlobalImprovement {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    (p : Problem X V) (q : Problem Y V) where
  /-- Map source feasible points to target feasible points. -/
  map : FeasiblePoint p → FeasiblePoint q
  /-- The target objective is no worse than the source objective. -/
  objective_le : ∀ x : FeasiblePoint p,
    q.objective (map x).1 ≤ p.objective x.1

namespace GlobalImprovement

/-- Every problem improves itself. -/
protected def refl {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) : GlobalImprovement p p where
  map := id
  objective_le := fun _ => le_rfl

/-- Compose two one-way global-improvement certificates. -/
def trans {X : Type u} {Y : Type v} {Z : Type w} {V : Type*} [Preorder V]
    {p : Problem X V} {q : Problem Y V} {r : Problem Z V}
    (pq : GlobalImprovement p q) (qr : GlobalImprovement q r) :
    GlobalImprovement p r where
  map := qr.map ∘ pq.map
  objective_le := fun x => le_trans (qr.objective_le (pq.map x)) (pq.objective_le x)

/-- A one-way certificate transports existence of a feasible point. -/
theorem map_hasFeasiblePoint
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (c : GlobalImprovement p q) :
    p.HasFeasiblePoint → q.HasFeasiblePoint := fun h => h.map c.map

/-- Unboundedness in the optimization direction is transported forward by a
one-way certificate. -/
theorem map_isUnbounded
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (c : GlobalImprovement p q) :
    p.IsUnbounded → q.IsUnbounded := by
  intro hp b
  obtain ⟨x, hx⟩ := hp b
  exact ⟨c.map x, lt_of_le_of_lt (c.objective_le x) hx⟩

end GlobalImprovement

/-- A certificate that two problems have the same global optimization
behavior.

The maps need not be inverse functions.  The paired objective inequalities are
the exact data needed for global-optimum and global-value preservation. -/
structure GlobalEquivalence {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    (p : Problem X V) (q : Problem Y V) where
  /-- A no-worse feasible map from the source to the target. -/
  forward : GlobalImprovement p q
  /-- A no-worse feasible map from the target back to the source. -/
  backward : GlobalImprovement q p

namespace GlobalEquivalence

/-- Forget the backward half of an equivalence, yielding the explicitly
oriented one-way certificate used by relaxation-style APIs. -/
def toGlobalImprovement
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q) :
    GlobalImprovement p q :=
  e.forward

/-- Global equivalence is reflexive. -/
protected def refl {X : Type u} {V : Type v} [Preorder V]
    (p : Problem X V) : GlobalEquivalence p p where
  forward := GlobalImprovement.refl p
  backward := GlobalImprovement.refl p

/-- Global equivalence is symmetric. -/
def symm {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q) :
    GlobalEquivalence q p where
  forward := e.backward
  backward := e.forward

/-- Global equivalence is transitive. -/
def trans {X : Type u} {Y : Type v} {Z : Type w} {V : Type*} [Preorder V]
    {p : Problem X V} {q : Problem Y V} {r : Problem Z V}
    (pq : GlobalEquivalence p q) (qr : GlobalEquivalence q r) :
    GlobalEquivalence p r where
  forward := pq.forward.trans qr.forward
  backward := qr.backward.trans pq.backward

/-- Equivalent problems are feasible simultaneously. -/
theorem hasFeasiblePoint_iff
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q) :
    p.HasFeasiblePoint ↔ q.HasFeasiblePoint :=
  ⟨e.forward.map_hasFeasiblePoint, e.backward.map_hasFeasiblePoint⟩

/-- Send a global optimum through the forward map of an equivalence. -/
theorem map_isGlobalOptimum
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q)
    {x : FeasiblePoint p} (hx : p.IsGlobalOptimum x) :
    q.IsGlobalOptimum (e.forward.map x) := by
  intro y
  calc
    q.objective (e.forward.map x).1 ≤ p.objective x.1 :=
      e.forward.objective_le x
    _ ≤ p.objective (e.backward.map y).1 := hx (e.backward.map y)
    _ ≤ q.objective y.1 := e.backward.objective_le y

/-- Send a global optimum through the backward map of an equivalence. -/
theorem map_isGlobalOptimum_backward
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q)
    {y : FeasiblePoint q} (hy : q.IsGlobalOptimum y) :
    p.IsGlobalOptimum (e.backward.map y) :=
  e.symm.map_isGlobalOptimum hy

/-- Equivalent problems attain a global optimum simultaneously. -/
theorem hasGlobalOptimum_iff
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q) :
    p.HasGlobalOptimum ↔ q.HasGlobalOptimum := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨e.forward.map x, e.map_isGlobalOptimum hx⟩
  · rintro ⟨y, hy⟩
    exact ⟨e.backward.map y, e.map_isGlobalOptimum_backward hy⟩

/-- Corresponding mapped optima have the same objective value. -/
theorem objective_eq_of_isGlobalOptimum
    {X : Type u} {Y : Type v} {V : Type w} [PartialOrder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q)
    {x : FeasiblePoint p} (hx : p.IsGlobalOptimum x) :
    q.objective (e.forward.map x).1 = p.objective x.1 := by
  apply le_antisymm (e.forward.objective_le x)
  exact le_trans (hx (e.backward.map (e.forward.map x)))
    (e.backward.objective_le (e.forward.map x))

/-- Any attained global optima of equivalent problems have the same value. -/
theorem objective_eq_of_optima
    {X : Type u} {Y : Type v} {V : Type w} [PartialOrder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q)
    {x : FeasiblePoint p} {y : FeasiblePoint q}
    (hx : p.IsGlobalOptimum x) (hy : q.IsGlobalOptimum y) :
    p.objective x.1 = q.objective y.1 := by
  apply le_antisymm
  · exact le_trans (hx (e.backward.map y)) (e.backward.objective_le y)
  · exact le_trans (hy (e.forward.map x)) (e.forward.objective_le x)

/-- Equivalent problems have exactly the same objective lower bounds. -/
theorem isObjectiveLowerBound_iff
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q)
    (b : V) : p.IsObjectiveLowerBound b ↔ q.IsObjectiveLowerBound b := by
  constructor
  · intro hp y
    exact le_trans (hp (e.backward.map y)) (e.backward.objective_le y)
  · intro hq x
    exact le_trans (hq (e.forward.map x)) (e.forward.objective_le x)

/-- Equivalent problems are unbounded in the optimization direction
simultaneously. -/
theorem isUnbounded_iff
    {X : Type u} {Y : Type v} {V : Type w} [Preorder V]
    {p : Problem X V} {q : Problem Y V} (e : GlobalEquivalence p q) :
    p.IsUnbounded ↔ q.IsUnbounded :=
  ⟨e.forward.map_isUnbounded, e.backward.map_isUnbounded⟩

end GlobalEquivalence

end PTran
