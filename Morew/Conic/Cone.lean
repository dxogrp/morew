/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Pi
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Convex cones and their ambient spaces

Each cone carries a finite-dimensional normed real vector space and a mathlib
`ConvexCone`, closed under addition and positive scaling. Mathlib's convention
allows empty cones and cones excluding zero; closedness is not required.
-/

namespace Morew.Conic

/-- A convex cone together with its finite-dimensional normed real ambient space.

Cone spaces live in `Type`; decision spaces may live in any universe. -/
structure Cone where
  /-- The real vector space containing this cone. -/
  Space : Type
  /-- The normed additive group on the cone space. -/
  [instNormedAddCommGroup : NormedAddCommGroup Space]
  /-- The normed real vector-space structure on the cone space. -/
  [instNormedSpace : NormedSpace ℝ Space]
  /-- The cone space is finite-dimensional. -/
  [instFiniteDimensional : FiniteDimensional ℝ Space]
  /-- The underlying cone and its closure under addition and positive scaling. -/
  carrier : ConvexCone ℝ Space

attribute [instance] Cone.instNormedAddCommGroup Cone.instNormedSpace
  Cone.instFiniteDimensional

namespace Cone

/-- The nonnegative cone in the real line. -/
noncomputable def nonnegativeScalar : Cone where
  Space := ℝ
  carrier := ConvexCone.positive ℝ ℝ

/-- The nonnegative real numbers as a `ConvexCone ℝ ℝ`. -/
noncomputable abbrev nonnegativeScalarCarrier : ConvexCone ℝ ℝ :=
  nonnegativeScalar.carrier

/-- The cone consisting of the zero vector in `Fin n → ℝ`.
Mathlib's `⊥` instead denotes the empty cone. -/
noncomputable def zero (n : Nat) : Cone where
  Space := Fin n → ℝ
  carrier := 0

/-- The coordinatewise nonnegative cone in `Fin n → ℝ`. -/
noncomputable def nonnegative (n : Nat) : Cone where
  Space := Fin n → ℝ
  carrier := ConvexCone.positive ℝ (Fin n → ℝ)

/-- Membership in the zero cone is equality with the zero vector. -/
@[simp]
theorem mem_zero {n : Nat} (x : Fin n → ℝ) :
    x ∈ (zero n).carrier ↔ x = 0 :=
  ConvexCone.mem_zero

/-- Membership in the nonnegative cone is coordinatewise nonnegativity. -/
@[simp]
theorem mem_nonnegative {n : Nat} (x : Fin n → ℝ) :
    x ∈ (nonnegative n).carrier ↔ ∀ i, 0 ≤ x i :=
  Iff.rfl

/-- Membership in the scalar nonnegative cone is ordinary nonnegativity. -/
@[simp]
theorem mem_nonnegativeScalar (x : ℝ) :
    x ∈ nonnegativeScalar.carrier ↔ 0 ≤ x :=
  Iff.rfl

end Cone

set_option quotPrecheck false in
/-- The cone of nonnegative real numbers. -/
notation (name := nonnegativeScalarCarrier) "ℝ₊" =>
  Morew.Conic.Cone.nonnegativeScalarCarrier

set_option quotPrecheck false in
/-- The cone of componentwise nonnegative vectors in dimension `n`. -/
notation:max (name := nonnegativeCarrier) "ℝ₊^" n:arg =>
  (Morew.Conic.Cone.nonnegative n).carrier

end Morew.Conic
