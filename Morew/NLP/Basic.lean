/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Morew.Core

/-!
# Certified smooth nonlinear programs

NLP data stores an objective and finitely many scalar residuals with closed
bounds, all C² on a common open domain containing every feasible point.
`Form` certifies equality with the represented problem.
-/

namespace Morew

universe u

namespace NLP

/-- Optional lower and upper bounds on a real residual, imposed non-strictly. -/
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

/-- Require `lower ≤ residual ≤ upper`. -/
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

/-- A lower bound requires `lower ≤ value`. -/
@[simp]
theorem contains_lowerBound (lower value : ℝ) :
    (lowerBound lower).Contains value ↔ lower ≤ value := by
  simp [Contains, lowerBound]

/-- An upper bound requires `value ≤ upper`. -/
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

/-- Two endpoints bound the residual from below and above. -/
@[simp]
theorem contains_between (lower upper value : ℝ) :
    (between lower upper).Contains value ↔ lower ≤ value ∧ value ≤ upper :=
  Iff.rfl

end Bounds

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A total scalar residual with closed bounds and a C² proof on an evaluation domain. -/
structure Row (domain : Set X) where
  /-- The total real-valued residual. -/
  residual : X → ℝ
  /-- Closed bounds imposed on the residual. -/
  bounds : Bounds
  /-- The residual is twice continuously differentiable on the domain. -/
  smooth : ContDiffOn ℝ 2 residual domain

/-- A row holds exactly when its residual satisfies its bounds. -/
def Row.Holds {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {domain : Set X} (row : Row X domain) (x : X) : Prop :=
  row.bounds.Contains (row.residual x)

/-- Finite-dimensional smooth nonlinear-program data.

The rows define feasibility and imply membership in the open evaluation domain.
Maximization uses `Problem X (OrderDual ℝ)` and sense `.maximize`, with the
original objective. The sense is stored separately because `OrderDual ℝ` is
definitionally equal to `ℝ`. -/
structure Data [FiniteDimensional ℝ X] where
  /-- The optimization direction. -/
  sense : ObjectiveSense
  /-- The common domain on which all stored smoothness proofs apply. -/
  domain : Set X
  /-- The evaluation domain is open. -/
  domain_isOpen : IsOpen domain
  /-- The total real-valued objective, with no sign change for maximization. -/
  objective : X → ℝ
  /-- The objective is twice continuously differentiable on the domain. -/
  objective_smooth : ContDiffOn ℝ 2 objective domain
  /-- The number of scalar constraints. -/
  rowCount : Nat
  /-- Every row uses the same evaluation domain. -/
  rows : Fin rowCount → Row X domain
  /-- Row feasibility supplies the domain needed by the smoothness proofs. -/
  feasible_mem_domain : ∀ x, (∀ i, (rows i).Holds x) → x ∈ domain

variable [FiniteDimensional ℝ X]

namespace Data

variable {X}

/-- The problem with the original objective and the conjunction of the stored rows.
Objective sense is supplied by the declaration's value type, as described in `Data`. -/
def toProblem (data : Data X) : Problem X ℝ where
  objective := data.objective
  feasible x := ∀ i, (data.rows i).Holds x

/-- Conversion preserves objective values at every point. -/
@[simp]
theorem toProblem_objective (data : Data X) (x : X) :
    data.toProblem.objective x = data.objective x := rfl

/-- Feasibility is exactly the conjunction of the stored rows. -/
@[simp]
theorem toProblem_feasible (data : Data X) (x : X) :
    data.toProblem.feasible x ↔ ∀ i, (data.rows i).Holds x := Iff.rfl

end Data

variable {X}

/-- A smooth NLP representation with the same objective and feasible set.
Equality includes objective values outside the evaluation domain. Objective
sense is stored separately in `Data.sense`. -/
structure Form (p : Problem X ℝ) where
  /-- The smooth nonlinear-program data. -/
  data : Data X
  /-- The objective and feasible predicate represent the problem exactly. -/
  represents : data.toProblem = p

end NLP

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]

/-- Existence of a certified smooth-NLP representation. `NLP.Form` carries the data. -/
def IsSmoothNLP (p : Problem X ℝ) : Prop :=
  Nonempty (NLP.Form p)

/-- A smooth NLP representation implies `IsSmoothNLP`. -/
theorem NLP.Form.isSmoothNLP {p : Problem X ℝ} (form : NLP.Form p) : IsSmoothNLP p :=
  ⟨form⟩

end Morew
