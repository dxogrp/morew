/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite geometric means and inverse products

These are ordinary total real functions. The empty geometric mean and inverse
product both equal one. Their exact conic representations separately require a
nonempty dimension and coordinatewise nonnegative or strictly positive inputs.
In particular, an inverse product with a zero factor is zero under real
division's totalized semantics, outside its intended positive modeling domain.
-/

namespace Morew.Fn

/-- The unweighted geometric mean of a finite real vector. Its usual domain is
coordinatewise nonnegative; the empty vector has value one. -/
noncomputable def geoMean {n : Nat} (xs : Fin n → ℝ) : ℝ :=
  Real.rpow (∏ i, xs i) (1 / (n : ℝ))

/-- The reciprocal of a finite product. Its intended modeling domain is
coordinatewise strictly positive; the empty vector has value one. -/
noncomputable def invProd {n : Nat} (xs : Fin n → ℝ) : ℝ :=
  (∏ i, xs i)⁻¹

/-- The geometric mean uses the native real power of the product. -/
theorem geoMean_eq_rpow_prod {n : Nat} (xs : Fin n → ℝ) :
    geoMean xs = Real.rpow (∏ i, xs i) (1 / (n : ℝ)) := rfl

/-- On nonnegative inputs, the geometric mean is also the product of the
coordinatewise roots. -/
theorem geoMean_eq_prod_rpow {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 ≤ xs i) :
    geoMean xs = ∏ i, Real.rpow (xs i) (1 / (n : ℝ)) :=
  (Real.finsetProd_rpow Finset.univ xs (fun i _ => hx i) _).symm

/-- The inverse product uses the native reciprocal of the product. -/
theorem invProd_eq_inv_prod {n : Nat} (xs : Fin n → ℝ) :
    invProd xs = (∏ i, xs i)⁻¹ := rfl

/-- The reciprocal of a product is the product of the reciprocals, including
the totalized zero cases. -/
theorem invProd_eq_prod_inv {n : Nat} (xs : Fin n → ℝ) :
    invProd xs = ∏ i, (xs i)⁻¹ := by
  simp [invProd]

/-- The empty geometric mean is one. -/
@[simp] theorem geoMean_empty (xs : Fin 0 → ℝ) : geoMean xs = 1 := by
  simp [geoMean]

/-- The empty inverse product is one. -/
@[simp] theorem invProd_empty (xs : Fin 0 → ℝ) : invProd xs = 1 := by
  simp [invProd]

/-- The geometric mean of a singleton is its coordinate. -/
@[simp] theorem geoMean_singleton (xs : Fin 1 → ℝ) : geoMean xs = xs 0 := by
  simp [geoMean]

/-- The inverse product of a singleton is its reciprocal. -/
@[simp] theorem invProd_singleton (xs : Fin 1 → ℝ) : invProd xs = (xs 0)⁻¹ := by
  simp [invProd]

/-- A geometric mean of nonnegative inputs is nonnegative. -/
theorem geoMean_nonneg {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 ≤ xs i) :
    0 ≤ geoMean xs :=
  Real.rpow_nonneg (Finset.prod_nonneg (fun i _ => hx i)) _

/-- A geometric mean of positive inputs is positive. -/
theorem geoMean_pos {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 < xs i) :
    0 < geoMean xs :=
  Real.rpow_pos_of_pos (Finset.prod_pos (fun i _ => hx i)) _

/-- A zero coordinate makes every nonempty geometric mean zero. -/
theorem geoMean_eq_zero {n : Nat} (xs : Fin n → ℝ) (i : Fin n) (hi : xs i = 0) :
    geoMean xs = 0 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt i.isLt)
  change (∏ j, xs j) ^ (1 / (n : ℝ)) = 0
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
  exact Real.zero_rpow (one_div_ne_zero hn)

/-- An inverse product is positive on its intended positive domain. -/
theorem invProd_pos {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 < xs i) :
    0 < invProd xs :=
  inv_pos.mpr (Finset.prod_pos (fun i _ => hx i))

end Morew.Fn
