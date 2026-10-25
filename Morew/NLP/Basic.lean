/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Morew.Core

/-!
# Smooth nonlinear-program bounds and rows

Closed residual bounds and domain-indexed C² rows for manual NLP representations.
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

end NLP

end Morew
