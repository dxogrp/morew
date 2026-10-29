/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.GeometricMean
import Mathlib.Tactic.NormNum

/-!
# Finite geometric-mean and inverse-product semantics

The checks include symbolic dimensions, the exact prefix layout at dimensions
one through three, arbitrary positions of zero coordinates, negative hypograph
bounds, and the strictly positive inverse-product domain. They use no elaborator
or reformulation commands.
-/

assert_not_exists Morew.Syntax.ProblemView

namespace MorewTest.Conic.PowerGeometricMean

noncomputable section

open Morew Morew.Conic Morew.Conic.Power

example (xs : Fin 0 → ℝ) : Fn.geoMean xs = 1 := Fn.geoMean_empty xs
example (xs : Fin 0 → ℝ) : Fn.invProd xs = 1 := Fn.invProd_empty xs
example (xs : Fin 1 → ℝ) : Fn.geoMean xs = xs 0 := Fn.geoMean_singleton xs
example (xs : Fin 1 → ℝ) : Fn.invProd xs = (xs 0)⁻¹ := Fn.invProd_singleton xs

example {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 ≤ xs i) :
    Fn.geoMean xs = ∏ i, Real.rpow (xs i) (1 / (n : ℝ)) :=
  Fn.geoMean_eq_prod_rpow xs hx

example {n : Nat} (xs : Fin n → ℝ) : Fn.invProd xs = ∏ i, (xs i)⁻¹ :=
  Fn.invProd_eq_prod_inv xs

example {n : Nat} (hn : 0 < n) :
    (geoMeanHypograph hn).Auxiliary = (Fin n → ℝ) := rfl

example {n : Nat} (hn : 0 < n) :
    (invProdEpigraph hn).Auxiliary = (Fin n → ℝ) := rfl

example {n : Nat} (hn : 0 < n) (xs : {xs : Fin n → ℝ // ∀ i, 0 ≤ xs i}) (t : ℝ) :
    t ≤ Fn.geoMean xs.1 ↔ ∃ u, (geoMeanHypograph hn).target xs t u :=
  (geoMeanHypograph hn).source_iff_exists xs t

example {n : Nat} (hn : 0 < n) (xs : {xs : Fin n → ℝ // ∀ i, 0 < xs i}) (t : ℝ) :
    Fn.invProd xs.1 ≤ t ↔ ∃ u, (invProdEpigraph hn).target xs t u :=
  (invProdEpigraph hn).source_iff_exists xs t

/-! The singleton has no chain cones and retains its fixed auxiliary. -/

example (x t : ℝ) (hx : 0 ≤ x) :
    t ≤ x ↔ ∃ u : Fin 1 → ℝ, u 0 = x ∧ 0 ≤ u 0 ∧ t ≤ u 0 := by
  simpa [Fin.forall_fin_succ] using
    le_geoMean_iff ![x] t (by decide) (by simpa using hx)

example (x t : ℝ) (hx : 0 < x) :
    x⁻¹ ≤ t ↔ ∃ u : Fin 1 → ℝ, u 0 = x ∧ (t, u 0, 1) ∈ POW (1 / 2) := by
  simpa [Fin.forall_fin_succ, one_add_one_eq_two] using
    invProd_le_iff ![x] t (by decide) (by simpa using hx)

/-! Concrete layouts check original coordinate order and all cone parameters. -/

example (x y t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    t ≤ Fn.geoMean ![x, y] ↔ ∃ u : Fin 2 → ℝ,
      u 0 = x ∧ (u 0, y, u 1) ∈ POW (1 / 2) ∧ 0 ≤ u 1 ∧ t ≤ u 1 := by
  simpa [Fin.forall_fin_succ] using
    le_geoMean_iff ![x, y] t (by decide) (by simpa using And.intro hx hy)

example (x y z t : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    t ≤ Fn.geoMean ![x, y, z] ↔ ∃ u : Fin 3 → ℝ,
      u 0 = x ∧
      ((u 0, y, u 1) ∈ POW (1 / 2) ∧ (u 1, z, u 2) ∈ POW (2 / 3)) ∧
      0 ≤ u 2 ∧ t ≤ u 2 := by
  have h := le_geoMean_iff ![x, y, z] t (by decide)
    (by simpa [Fin.forall_fin_succ] using And.intro hx (And.intro hy hz))
  norm_num [Fin.forall_fin_succ] at h ⊢
  exact h

example (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Fn.invProd ![x, y, z] ≤ t ↔ ∃ u : Fin 3 → ℝ,
      u 0 = x ∧
      ((u 0, y, u 1) ∈ POW (1 / 2) ∧ (u 1, z, u 2) ∈ POW (2 / 3)) ∧
      (t, u 2, 1) ∈ POW (1 / 4) := by
  have h := invProd_le_iff ![x, y, z] t (by decide)
    (by simpa [Fin.forall_fin_succ] using And.intro hx (And.intro hy hz))
  norm_num [Fin.forall_fin_succ] at h ⊢
  exact h

/-! Any zero position is allowed, including with a negative lower bound. -/

example {n : Nat} (hn : 0 < n) (xs : Fin n → ℝ) (hx : ∀ i, 0 ≤ xs i)
    (i : Fin n) (hi : xs i = 0) (t : ℝ) (ht : t ≤ 0) :
    ∃ u, (geoMeanHypograph hn).target ⟨xs, hx⟩ t u := by
  apply ((geoMeanHypograph hn).source_iff_exists ⟨xs, hx⟩ t).mp
  simpa only [Fn.geoMean_eq_zero xs i hi] using ht

example (xs : Fin 3 → ℝ) (hx : ∀ i, 0 ≤ xs i) (i : Fin 3) (hi : xs i = 0) :
    ¬ ∃ u, (geoMeanHypograph (by decide : 0 < 3)).target ⟨xs, hx⟩ 1 u := by
  intro h
  have hsource := ((geoMeanHypograph (by decide : 0 < 3)).source_iff_exists _ _).mpr h
  norm_num [Fn.geoMean_eq_zero xs i hi] at hsource

example : ∃ u, (geoMeanHypograph (by decide : 0 < 3)).target
    ⟨![0, 4, 9], by norm_num [Fin.forall_fin_succ]⟩ (-2) u := by
  apply ((geoMeanHypograph (by decide : 0 < 3)).source_iff_exists _ _).mp
  rw [Fn.geoMean_eq_zero _ 0 (by simp)]
  norm_num

example : ∃ u, (geoMeanHypograph (by decide : 0 < 3)).target
    ⟨![4, 0, 9], by norm_num [Fin.forall_fin_succ]⟩ 0 u := by
  apply ((geoMeanHypograph (by decide : 0 < 3)).source_iff_exists _ _).mp
  rw [Fn.geoMean_eq_zero _ 1 (by simp)]

example : ∃ u, (geoMeanHypograph (by decide : 0 < 3)).target
    ⟨![4, 9, 0], by norm_num [Fin.forall_fin_succ]⟩ (-1) u := by
  apply ((geoMeanHypograph (by decide : 0 < 3)).source_iff_exists _ _).mp
  rw [Fn.geoMean_eq_zero _ 2 (by simp)]
  norm_num

/-! Positive inverse products retain exact thresholds and reject nonpositive bounds. -/

example : ∃ u, (invProdEpigraph (by decide : 0 < 3)).target
    ⟨![2, 3, 4], by norm_num [Fin.forall_fin_succ]⟩ (1 / 24) u := by
  apply ((invProdEpigraph (by decide : 0 < 3)).source_iff_exists _ _).mp
  norm_num [Fn.invProd, Fin.prod_univ_succ]

example : ¬ ∃ u, (invProdEpigraph (by decide : 0 < 3)).target
    ⟨![2, 3, 4], by norm_num [Fin.forall_fin_succ]⟩ (1 / 25) u := by
  intro h
  have hsource := ((invProdEpigraph (by decide : 0 < 3)).source_iff_exists _ _).mpr h
  norm_num [Fn.invProd, Fin.prod_univ_succ] at hsource

example {n : Nat} (hn : 0 < n) (xs : Fin n → ℝ) (hx : ∀ i, 0 < xs i)
    (t : ℝ) (ht : t ≤ 0) :
    ¬ ∃ u, (invProdEpigraph hn).target ⟨xs, hx⟩ t u := by
  rw [← (invProdEpigraph hn).source_iff_exists]
  exact not_le.mpr (lt_of_le_of_lt ht (Fn.invProd_pos xs hx))

/-! The raw zero case is different, which is why inverse-product records
cannot relax their strictly positive domain to nonnegative coordinates. -/

example : Fn.invProd ![0, 2] = 0 := by norm_num [Fn.invProd, Fin.prod_univ_succ]
example (t : ℝ) : (t, 0, 1) ∉ POW (1 / 3) := by norm_num

end

end MorewTest.Conic.PowerGeometricMean
