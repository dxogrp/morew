/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Logic.Basic

/-!
# Exact constraint representations

Predicate, graph, epigraph, and hypograph representations by existential
equivalences, shared by conic and smooth NLP reformulations.
-/

namespace Morew

universe u v w z

/-- Represent `source x` by an existential predicate `∃ a, target x a`. -/
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

/-- Construct a representation from a pointwise equivalence, using `Unit`
for the auxiliary type. -/
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

/-- Represent the graph equation `y = f x` by `∃ a, target x y a`. -/
structure GraphRepresentation {X : Type u} {Y : Type v} (f : X → Y) where
  /-- The type of auxiliary values used by the representation. -/
  Auxiliary : Type w
  /-- The represented graph predicate. -/
  target : X → Y → Auxiliary → Prop
  /-- The represented predicate is existentially equivalent to the graph
  equation. -/
  source_iff_exists : ∀ x y, y = f x ↔ ∃ a, target x y a

namespace GraphRepresentation

/-- Apply a graph representation to expressions on a decision space. -/
def toExactConstraintLift {X : Type u} {Y : Type v} {Z : Type z} {f : X → Y}
    (representation : GraphRepresentation.{u, v, w} f)
    (input : Z → X) (output : Z → Y) :
    ExactConstraintLift (fun point => output point = f (input point)) where
  Auxiliary := representation.Auxiliary
  target point := representation.target (input point) (output point)
  source_iff_exists point :=
    representation.source_iff_exists (input point) (output point)

/-- Apply a graph representation to the equation `f x = y` on a decision space. -/
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

/-- Represent the epigraph predicate `f x ≤ t` by `∃ a, target x t a`. -/
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

/-- Apply an epigraph representation to expressions on a decision space. -/
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

/-- Represent the hypograph predicate `t ≤ f x` by `∃ a, target x t a`. -/
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

/-- Apply a hypograph representation to expressions on a decision space. -/
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

end Morew
