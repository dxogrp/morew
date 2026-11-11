/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Cone
import Morew.Core

/-!
# Certified affine cone programs

Conic data records an affine objective and finitely many affine cone constraints.
`Conic.Form p` certifies that these data represent `p`.
-/

namespace Morew

universe u

namespace Conic

variable (X : Type u) [AddCommGroup X] [Module ℝ X]

/-- An affine map constrained to lie in a convex cone. -/
structure Constraint where
  /-- The target convex cone and its ambient space. -/
  cone : Cone
  /-- The affine map from decision points into the cone space. -/
  map : X →ᵃ[ℝ] cone.Space

namespace Constraint

variable {X}

/-- A row holds when its affine image lies in its cone. -/
def Holds (c : Constraint X) (x : X) : Prop :=
  c.map x ∈ c.cone.carrier

/-- Constrain an affine map to vanish. -/
def eqZero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (f : X →ᵃ[ℝ] Y) : Constraint X where
  cone := { Space := Y, carrier := 0 }
  map := f

/-- Constrain an affine map to be nonnegative. For finite vectors, the order is
componentwise. -/
def nonneg {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [PartialOrder Y] [IsOrderedAddMonoid Y]
    [PosSMulMono ℝ Y] (f : X →ᵃ[ℝ] Y) : Constraint X where
  cone := { Space := Y, carrier := ConvexCone.positive ℝ Y }
  map := f

/-- A zero-cone row holds exactly when the affine map vanishes. -/
@[simp]
theorem holds_eqZero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (f : X →ᵃ[ℝ] Y) (x : X) :
    (eqZero f).Holds x ↔ f x = 0 :=
  Iff.rfl

/-- A nonnegative-cone row holds exactly when its affine image is nonnegative. -/
@[simp]
theorem holds_nonneg {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [PartialOrder Y] [IsOrderedAddMonoid Y]
    [PosSMulMono ℝ Y] (f : X →ᵃ[ℝ] Y) (x : X) :
    (nonneg f).Holds x ↔ 0 ≤ f x :=
  Iff.rfl

/-- The feasible set of an affine cone-membership row is convex. -/
theorem feasibleSetConvex (c : Constraint X) :
    Convex ℝ {x | c.Holds x} :=
  Convex.affine_preimage c.map c.cone.carrier.convex

end Constraint

/-- Finite-dimensional affine cone-program data.

Maximization uses `Problem X (OrderDual ℝ)` and sense `.maximize`. The sense
is stored separately because `OrderDual ℝ` is definitionally equal to `ℝ`. -/
structure Data [FiniteDimensional ℝ X] where
  /-- The optimization direction. -/
  sense : ObjectiveSense
  /-- The affine real-valued objective. -/
  objective : X →ᵃ[ℝ] ℝ
  /-- The number of cone constraints. -/
  rowCount : Nat
  /-- The rows, whose cone spaces may have different dimensions. -/
  constraints : Fin rowCount → Constraint X

variable [FiniteDimensional ℝ X]

namespace Data

variable {X}

/-- The problem with the stored objective and row predicates. Its objective
sense is supplied by the declaration's value type, as described in `Data`. -/
def toProblem (data : Data X) : Problem X ℝ where
  objective := data.objective
  feasible x := ∀ i, (data.constraints i).Holds x

/-- Conversion to a problem preserves the objective exactly. -/
@[simp]
theorem toProblem_objective (data : Data X) (x : X) :
    data.toProblem.objective x = data.objective x := rfl

/-- Conversion to a problem requires exactly all stored rows. -/
@[simp]
theorem toProblem_feasible (data : Data X) (x : X) :
    data.toProblem.feasible x ↔ ∀ i, (data.constraints i).Holds x := Iff.rfl

/-- The feasible set of an affine cone program is convex. -/
theorem feasibleSetConvex (data : Data X) :
    Convex ℝ {x | data.toProblem.feasible x} := by
  simpa only [toProblem_feasible, Set.ofPred_forall] using
    convex_iInter (fun i => (data.constraints i).feasibleSetConvex)

end Data

variable {X}

/-- A conic representation with the same objective and feasible set.
Objective sense is stored separately in `Data.sense`. -/
structure Form (p : Problem X ℝ) where
  /-- The affine cone-program data. -/
  data : Data X
  /-- The stored data represents the entire problem exactly. -/
  represents : data.toProblem = p

end Conic

variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  [FiniteDimensional ℝ X]

/-- Existence of a certified conic representation. `Conic.Form` carries the data. -/
def IsConic (p : Problem X ℝ) : Prop :=
  Nonempty (Conic.Form p)

/-- A conic representation implies `IsConic`. -/
theorem Conic.Form.isConic {p : Problem X ℝ} (form : Conic.Form p) : IsConic p :=
  ⟨form⟩

end Morew
