/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Cone
import Morew.Core

/-!
# Certified affine cone programs

Conic data records an affine objective and finitely many affine cone-membership
rows. A `Conic.Form p` retains this data and an equality with the represented
`Problem`, independently of any source-to-target global-equivalence certificate.
Decision spaces require only real vector-space structure; no ambient norm is
part of a conic certificate. Cone spaces retain their bundled normed structures.

Objective sense is explicit data. Equality of `Problem` values cannot recover
it, since `OrderDual ℝ` is a reducible synonym for `ℝ`. Maximizing problems must
retain their explicit `OrderDual` type and use data with sense `.maximize`.
-/

namespace Morew

universe u

namespace Conic

variable (X : Type u) [AddCommGroup X] [Module ℝ X]

/-- An affine membership constraint in a bundled convex cone. -/
structure Constraint where
  /-- The target cone, including its vector space and checked cone laws. -/
  cone : Cone
  /-- The affine map from decision points into the cone space. -/
  map : X →ᵃ[ℝ] cone.Space

namespace Constraint

variable {X}

/-- A row holds when its affine image lies in its cone. -/
def Holds (c : Constraint X) (x : X) : Prop :=
  c.map x ∈ c.cone.carrier

/-- The zero-cone row for an affine map. In particular, scalar and finite-vector
maps can be used directly, without a one-coordinate scalar embedding. -/
def eqZero {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (f : X →ᵃ[ℝ] Y) : Constraint X where
  cone := { Space := Y, carrier := 0 }
  map := f

/-- The nonnegative-cone row for an affine map into an ordered real vector
space. For finite vectors, the order is coordinatewise. -/
def nonnegative {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
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
theorem holds_nonnegative {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [PartialOrder Y] [IsOrderedAddMonoid Y]
    [PosSMulMono ℝ Y] (f : X →ᵃ[ℝ] Y) (x : X) :
    (nonnegative f).Holds x ↔ 0 ≤ f x :=
  Iff.rfl

/-- The feasible set of an affine cone-membership row is convex. -/
theorem feasibleSetConvex (c : Constraint X) :
    Convex ℝ {x | c.Holds x} :=
  Convex.affine_preimage c.map c.cone.carrier.convex

end Constraint

/-- Finite-dimensional affine cone-program data.

The objective sense is recorded explicitly for consumers. It does not change
the objective function or feasible predicate returned by `toProblem`. -/
structure Data [FiniteDimensional ℝ X] where
  /-- Whether consumers should minimize or maximize the objective. -/
  sense : ObjectiveSense
  /-- The affine real-valued objective. -/
  objective : X →ᵃ[ℝ] ℝ
  /-- The number of cone-membership rows, possibly zero. -/
  rowCount : Nat
  /-- The rows, whose cone spaces may have different dimensions. -/
  constraints : Fin rowCount → Constraint X

variable [FiniteDimensional ℝ X]

namespace Data

variable {X}

/-- The ordinary problem with exactly the stored objective and row predicates.
The returned type does not encode `sense`; maximizing declarations retain an
explicit `Problem X (OrderDual ℝ)` type at their declaration site. -/
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

/-- The feasible set of an affine cone program is convex, including when
there are no rows. -/
theorem feasibleSetConvex (data : Data X) :
    Convex ℝ {x | data.toProblem.feasible x} := by
  simpa only [toProblem_feasible, Set.ofPred_forall] using
    convex_iInter (fun i => (data.constraints i).feasibleSetConvex)

end Data

variable {X}

/-- Concrete conic data representing a problem exactly.

The equality certifies the objective and feasibility, not agreement of the
recorded sense with a source declaration. Keep `.maximize` explicit when the
problem is declared with values in `OrderDual ℝ`. -/
structure Form (p : Problem X ℝ) where
  /-- The concrete affine cone-program data. -/
  data : Data X
  /-- The stored data represents the entire problem exactly. -/
  represents : data.toProblem = p

end Conic

variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  [FiniteDimensional ℝ X]

/-- A proposition asserting the existence of a certified conic representation.
Use `Conic.Form` directly when the concrete representation is needed. -/
def IsConic (p : Problem X ℝ) : Prop :=
  Nonempty (Conic.Form p)

/-- A concrete certified conic form witnesses conic representability. -/
theorem Conic.Form.isConic {p : Problem X ℝ} (form : Conic.Form p) : IsConic p :=
  ⟨form⟩

end Morew
