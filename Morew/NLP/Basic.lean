/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Morew.Core

/-!
# Certified smooth nonlinear programs

NLP data stores a real objective, finitely many scalar residuals with closed
bounds, and their C² proofs on a common open evaluation domain. Every point
satisfying the rows must belong to that domain. The domain is proof data: it
is not an extra constraint in `Data.toProblem`.

Objectives and residuals remain total functions. `Form.represents` equates the
entire represented problem, including objective values outside the evaluation
domain. No convexity assumption is imposed on either the objective or the rows.

With zero rows, every point is feasible, so the domain must contain all points.
An empty domain is permitted when the rows are infeasible; smoothness on that
domain is vacuous. Inconsistent bounds are therefore valid representations.

Objective sense follows the conic API: maximizing problems retain an explicit
`Problem X (OrderDual ℝ)` type and data with sense `.maximize`. Since `OrderDual`
is a reducible synonym, representation equality alone does not certify the
recorded sense. Conversion never negates the objective.
-/

namespace Morew

universe u

namespace NLP

/-- Optional closed lower and upper bounds on a real residual.
Absent endpoints impose no condition; inconsistent endpoints are permitted. -/
structure Bounds where
  /-- A closed lower bound, or no lower bound. -/
  lower : Option ℝ
  /-- A closed upper bound, or no upper bound. -/
  upper : Option ℝ

namespace Bounds

/-- Impose no restriction on the residual. -/
def unbounded : Bounds := ⟨none, none⟩

/-- Require the residual to be at least `lower`. -/
def lowerBound (lower : ℝ) : Bounds := ⟨some lower, none⟩

/-- Require the residual to be at most `upper`. -/
def upperBound (upper : ℝ) : Bounds := ⟨none, some upper⟩

/-- Require the residual to equal `value`. -/
def fixed (value : ℝ) : Bounds := ⟨some value, some value⟩

/-- Require both closed bounds, without assuming `lower ≤ upper`. -/
def between (lower upper : ℝ) : Bounds := ⟨some lower, some upper⟩

/-- A value satisfies every endpoint that is present. -/
def Contains (bounds : Bounds) (value : ℝ) : Prop :=
  (match bounds.lower with
    | none => True
    | some lower => lower ≤ value) ∧
  (match bounds.upper with
    | none => True
    | some upper => value ≤ upper)

/-- Every real value satisfies unbounded bounds. -/
@[simp]
theorem contains_unbounded (value : ℝ) : unbounded.Contains value :=
  ⟨trivial, trivial⟩

/-- A lower bound is a closed lower comparison. -/
@[simp]
theorem contains_lowerBound (lower value : ℝ) :
    (lowerBound lower).Contains value ↔ lower ≤ value := by
  simp [Contains, lowerBound]

/-- An upper bound is a closed upper comparison. -/
@[simp]
theorem contains_upperBound (upper value : ℝ) :
    (upperBound upper).Contains value ↔ value ≤ upper := by
  simp [Contains, upperBound]

/-- Equal lower and upper bounds require equality with the fixed value. -/
@[simp]
theorem contains_fixed (fixedValue value : ℝ) :
    (fixed fixedValue).Contains value ↔ value = fixedValue := by
  change fixedValue ≤ value ∧ value ≤ fixedValue ↔ value = fixedValue
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩

/-- Two endpoints impose their closed comparisons in lower/upper order. -/
@[simp]
theorem contains_between (lower upper value : ℝ) :
    (between lower upper).Contains value ↔ lower ≤ value ∧ value ≤ upper :=
  Iff.rfl

end Bounds

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A scalar residual with closed bounds and a C² proof on an evaluation domain.
The residual is a total function; no affinity or convexity is required. -/
structure Row (domain : Set X) where
  /-- The total real-valued residual. -/
  residual : X → ℝ
  /-- Closed bounds imposed on the residual. -/
  bounds : Bounds
  /-- The residual is twice continuously differentiable on the domain. -/
  smooth : ContDiffOn ℝ 2 residual domain

/-- A row holds exactly when its residual satisfies its bounds.
Domain membership is not part of this predicate. -/
def Row.Holds {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {domain : Set X} (row : Row X domain) (x : X) : Prop :=
  row.bounds.Contains (row.residual x)

/-- Finite-dimensional smooth nonlinear-program data.
The rows alone define feasibility and must imply membership in the open domain. -/
structure Data [FiniteDimensional ℝ X] where
  /-- Whether consumers should minimize or maximize the objective. -/
  sense : ObjectiveSense
  /-- The common domain on which all stored smoothness proofs apply. -/
  domain : Set X
  /-- The evaluation domain is open. -/
  domain_isOpen : IsOpen domain
  /-- The total real-valued objective, with no sign change for maximization. -/
  objective : X → ℝ
  /-- The objective is twice continuously differentiable on the domain. -/
  objective_smooth : ContDiffOn ℝ 2 objective domain
  /-- The number of scalar rows, possibly zero. -/
  rowCount : Nat
  /-- Every row uses the same evaluation domain. -/
  rows : Fin rowCount → Row X domain
  /-- Row feasibility supplies the domain needed by the smoothness proofs. -/
  feasible_mem_domain : ∀ x, (∀ i, (rows i).Holds x) → x ∈ domain

variable [FiniteDimensional ℝ X]

namespace Data

variable {X}

/-- The ordinary problem with the unchanged objective and exactly the stored rows.
The domain is not conjoined to feasibility. The returned type does not encode
`sense`; maximizing declarations retain an explicit `OrderDual ℝ` value type. -/
def toProblem (data : Data X) : Problem X ℝ where
  objective := data.objective
  feasible x := ∀ i, (data.rows i).Holds x

/-- Conversion preserves objective values at every point. -/
@[simp]
theorem toProblem_objective (data : Data X) (x : X) :
    data.toProblem.objective x = data.objective x := rfl

/-- Conversion requires exactly the rows, without an additional domain test. -/
@[simp]
theorem toProblem_feasible (data : Data X) (x : X) :
    data.toProblem.feasible x ↔ ∀ i, (data.rows i).Holds x := Iff.rfl

end Data

variable {X}

/-- Concrete smooth-NLP data representing an entire problem exactly.
Equality includes the objective outside the domain, but cannot certify agreement
of the separately recorded objective sense with a source declaration. -/
structure Form (p : Problem X ℝ) where
  /-- The concrete smooth nonlinear-program representation. -/
  data : Data X
  /-- The objective and feasible predicate represent the problem exactly. -/
  represents : data.toProblem = p

end NLP

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- Existence of a certified smooth-NLP representation.
Retain an `NLP.Form` directly when the concrete data is needed. -/
def IsSmoothNLP (p : Problem X ℝ) : Prop :=
  Nonempty (NLP.Form p)

/-- A concrete certified form witnesses smooth-NLP representability. -/
theorem NLP.Form.isSmoothNLP {p : Problem X ℝ} (form : NLP.Form p) : IsSmoothNLP p :=
  ⟨form⟩

end Morew
