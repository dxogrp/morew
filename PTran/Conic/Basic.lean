import PTran.Conic.Cone
import PTran.Core

/-!
# Certified affine cone programs

Conic data records an affine objective and finitely many affine cone-membership
rows. A `Conic.Form p` retains this data and an equality with the represented
`Problem`, independently of any source-to-target global-equivalence certificate.

Objective sense is explicit data. Equality of `Problem` values cannot recover
it, since `OrderDual ℝ` is a reducible synonym for `ℝ`. Maximizing problems must
retain their explicit `OrderDual` type and use data with sense `.maximize`.
-/

namespace PTran

universe u

namespace Conic

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

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

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- A proposition asserting the existence of a certified conic representation.
Use `Conic.Form` directly when the concrete representation is needed. -/
def IsConic (p : Problem X ℝ) : Prop :=
  Nonempty (Conic.Form p)

/-- A concrete certified conic form witnesses conic representability. -/
theorem Conic.Form.isConic {p : Problem X ℝ} (form : Conic.Form p) : IsConic p :=
  ⟨form⟩

end PTran
