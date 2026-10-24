/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Imported helpers for affine expansion regressions

Keep these definitions in a separate module to exercise declaration parameters,
universe instantiation, and finite evidence stored only inside helper bodies.
-/

namespace MorewTest.Affine.HelperFixtures

open Matrix
open scoped BigOperators

noncomputable section

def cost (a b x : ℝ) : ℝ := a * x + b

def residual (a b x : ℝ) : ℝ := a * x - b

abbrev shift (x : ℝ) : ℝ := x + 1

def nestedCost (a b x : ℝ) : ℝ := shift (cost a b x)

def ignored (_x : ℝ) : ℝ := 7

def discard (value _unused : ℝ) : ℝ := value

def constantFactor (a _x : ℝ) : ℝ := a

def quotient (a x : ℝ) : ℝ := x / a

def checkedQuotient (a : ℝ) (_h : a ≠ 0) (x : ℝ) : ℝ := x / a

def evidencedQuotient (a : ℝ) (h : a ≠ 0 ∧ True) (x : ℝ) : ℝ :=
  let _nonzero : a ≠ 0 := h.1
  x / a

def taggedCost {α : Type u} (_tag : α) (x : ℝ) : ℝ := x + 1

section
variable (a b : ℝ)

def sectionCost (x : ℝ) : ℝ := a * x + b

end

def vector (x : ℝ) : Fin 2 → ℝ := ![cost 2 1 x, -x]

def productCost (point : ℝ × ℝ) : ℝ × ℝ :=
  (cost 2 1 point.1, point.2 - point.1)

def matrixProduct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℝ) : Fin m → ℝ := A *ᵥ x

def rowProduct {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) : Fin n → ℝ := x ᵥ* A

def dot {n : ℕ} (a x : Fin n → ℝ) : ℝ := a ⬝ᵥ x

def total {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, cost 2 1 (x i)

def finiteDot {ι : Type u} (e : Fin 2 ≃ ι) (a x : ι → ℝ) : ℝ :=
  letI := Fintype.ofEquiv (Fin 2) e
  a ⬝ᵥ x

def finiteCoordinate {ι : Type u} (h : Finite ι ∧ True) (i : ι)
    (x : ι → ℝ) : ℝ :=
  let _finiteEvidence : Finite ι := h.1
  x i + 1

def finiteMatrix {ι : Type u} (e : Fin 2 ≃ ι) (A : Matrix ι ι ℝ)
    (x : ι → ℝ) : ι → ℝ :=
  letI := Fintype.ofEquiv (Fin 2) e
  A *ᵥ x

def hiddenProduct (x : ℝ) : ℝ := x * x

def hiddenDivision (x : ℝ) : ℝ := x / (x + 1)

def hiddenExponential (x : ℝ) : ℝ := Real.exp x

def helperPredicate (x : ℝ) : Prop := cost 2 1 x ≤ 10

def hiddenChangedAdd (x : ℝ) : ℝ :=
  @HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a * b⟩ x x

def hiddenCoercion (x : ℝ) : ℝ :=
  @Coe.coe ℝ ℝ ⟨fun a => a * a⟩ x

@[irreducible] def sealedCost (x : ℝ) : ℝ := x + 1

opaque opaqueCost (x : ℝ) : ℝ := x + 1

def recursiveCost : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => recursiveCost n x + 1

end

end MorewTest.Affine.HelperFixtures
