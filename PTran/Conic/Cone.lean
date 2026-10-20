import Mathlib.Algebra.Order.Pi
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Convex.Cone.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Bundled convex cones

Each cone carries a finite-dimensional normed real vector space and a mathlib
`ConvexCone`. The cone laws are checked proofs, not a classification tag.
Custom cones need not be closed, nonempty, or contain zero.
-/

namespace PTran.Conic

/-- A convex cone in a bundled finite-dimensional normed real vector space.

Cone spaces live in `Type`; decision spaces may live in any universe.
This keeps the cone-space universe out of the classification `PTran.IsConic`. -/
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

/-- The zero cone in `Fin n → ℝ`. Its carrier is the singleton zero vector,
not the empty cone denoted by mathlib's `⊥`. -/
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

end Cone
end PTran.Conic
