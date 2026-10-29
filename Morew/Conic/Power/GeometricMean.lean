/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Basic
import Morew.Fn.Power
import Morew.Rewrite.Basic

/-!
# Finite geometric-mean and inverse-product representations

A deterministic left-to-right chain bounds each auxiliary by the corresponding
prefix mean. The forward witnesses attain those bounds. The first auxiliary
equals the first input; each remaining coordinate is connected by a power cone. This uniform
layout works for symbolic nonempty dimensions without conditional coordinates.
Hypographs retain negative lower bounds, and all geometric-mean zero boundaries
are included. Inverse products require strictly positive input coordinates.
-/

namespace Morew.Conic.Power

/-- Every successive prefix-mean weight lies strictly between zero and one. -/
theorem prefixExponent_range (j : Nat) :
    0 < ((j : ℝ) + 1) / ((j : ℝ) + 2) ∧
      ((j : ℝ) + 1) / ((j : ℝ) + 2) < 1 := by
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hd : 0 < (j : ℝ) + 2 := by linarith
  exact ⟨div_pos (by linarith) hd, (div_lt_one hd).mpr (by linarith)⟩

private theorem geoMean_succ {k : Nat} (hk : 0 < k) (xs : Fin (k + 1) → ℝ)
    (hx : ∀ i, 0 ≤ xs i) :
    Fn.geoMean xs =
      Fn.geoMean (fun i : Fin k => xs i.castSucc) ^ ((k : ℝ) / ((k : ℝ) + 1)) *
        xs (Fin.last k) ^ (1 - (k : ℝ) / ((k : ℝ) + 1)) := by
  have hp : 0 ≤ ∏ i : Fin k, xs i.castSucc :=
    Finset.prod_nonneg (fun i _ => hx i.castSucc)
  have hk₀ : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hk)
  have hk₁ : (k : ℝ) + 1 ≠ 0 := by positivity
  change (∏ i, xs i) ^ (1 / ((k + 1 : Nat) : ℝ)) =
    ((∏ i : Fin k, xs i.castSucc) ^ (1 / (k : ℝ))) ^
      ((k : ℝ) / ((k : ℝ) + 1)) *
      xs (Fin.last k) ^ (1 - (k : ℝ) / ((k : ℝ) + 1))
  rw [Fin.prod_univ_castSucc, Real.mul_rpow hp (hx _), ← Real.rpow_mul hp]
  push_cast
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp
    ring

private def prefixVector {n : Nat} (xs : Fin n → ℝ) (k : Nat) (hk : k ≤ n) : Fin k → ℝ :=
  fun i => xs ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

private noncomputable def prefixMean {n : Nat} (xs : Fin n → ℝ) (i : Fin n) : ℝ :=
  Fn.geoMean (prefixVector xs (i.val + 1) (Nat.succ_le_of_lt i.isLt))

private theorem prefixMean_nonneg {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 ≤ xs i)
    (i : Fin n) : 0 ≤ prefixMean xs i :=
  Fn.geoMean_nonneg _ (fun _ => hx _)

private theorem prefixMean_first {n : Nat} (xs : Fin n → ℝ) (hn : 0 < n) :
    prefixMean xs ⟨0, hn⟩ = xs ⟨0, hn⟩ := by
  simp [prefixMean, prefixVector]

private theorem prefixMean_last {n : Nat} (xs : Fin n → ℝ) (hn : 0 < n) :
    prefixMean xs ⟨n - 1, by omega⟩ = Fn.geoMean xs := by
  cases n with
  | zero => omega
  | succ n => rfl

private theorem prefixMean_step {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 ≤ xs i)
    (j : Fin (n - 1)) :
    prefixMean xs ⟨j.val + 1, by omega⟩ =
      prefixMean xs ⟨j.val, by omega⟩ ^ (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2)) *
        xs ⟨j.val + 1, by omega⟩ ^
          (1 - ((j.val : ℝ) + 1) / ((j.val : ℝ) + 2)) := by
  have h := geoMean_succ (by omega : 0 < j.val + 1)
    (prefixVector xs (j.val + 1 + 1) (by omega)) (fun _ => hx _)
  convert h using 1 <;>
    simp only [prefixMean, prefixVector, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two, Fin.val_castSucc, Fin.val_last]
  rfl

private theorem chain_bound {n : Nat} (xs u : Fin n → ℝ) (hn : 0 < n)
    (hx : ∀ i, 0 ≤ xs i) (hfirst : u ⟨0, hn⟩ = xs ⟨0, hn⟩)
    (hchain : ∀ j : Fin (n - 1),
      (u ⟨j.val, by omega⟩, xs ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
        POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) :
    u ⟨n - 1, by omega⟩ ≤ Fn.geoMean xs := by
  have hbound : ∀ k (hk : k < n), u ⟨k, hk⟩ ≤ prefixMean xs ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [prefixMean_first xs hk]
      exact hfirst.le
    | succ k ih =>
      intro hk
      obtain ⟨hu, _, hcone⟩ := hchain ⟨k, by omega⟩
      have hmono := Real.rpow_le_rpow hu (ih (by omega)) (prefixExponent_range k).1.le
      calc
        u ⟨k + 1, hk⟩ ≤ |u ⟨k + 1, hk⟩| := le_abs_self _
        _ ≤ u ⟨k, by omega⟩ ^ (((k : ℝ) + 1) / ((k : ℝ) + 2)) *
            xs ⟨k + 1, hk⟩ ^ (1 - ((k : ℝ) + 1) / ((k : ℝ) + 2)) := hcone
        _ ≤ prefixMean xs ⟨k, by omega⟩ ^ (((k : ℝ) + 1) / ((k : ℝ) + 2)) *
            xs ⟨k + 1, hk⟩ ^ (1 - ((k : ℝ) + 1) / ((k : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (hx _) _)
        _ = prefixMean xs ⟨k + 1, hk⟩ := (prefixMean_step xs hx ⟨k, by omega⟩).symm
  simpa only [prefixMean_last xs hn] using hbound (n - 1) (by omega)

private theorem prefixMean_mem {n : Nat} (xs : Fin n → ℝ) (hx : ∀ i, 0 ≤ xs i)
    (j : Fin (n - 1)) :
    (prefixMean xs ⟨j.val, by omega⟩, xs ⟨j.val + 1, by omega⟩,
      prefixMean xs ⟨j.val + 1, by omega⟩) ∈
        POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2)) := by
  refine ⟨prefixMean_nonneg xs hx _, hx _, ?_⟩
  rw [abs_of_nonneg (prefixMean_nonneg xs hx _), prefixMean_step xs hx j]

/-- A finite geometric-mean hypograph has an exact prefix-chain lift. The
nonnegative final auxiliary, rather than the possibly negative bound, is the
last power-cone coordinate. -/
theorem le_geoMean_iff {n : Nat} (xs : Fin n → ℝ) (t : ℝ) (hn : 0 < n)
    (hx : ∀ i, 0 ≤ xs i) :
    t ≤ Fn.geoMean xs ↔ ∃ u : Fin n → ℝ,
      u ⟨0, hn⟩ = xs ⟨0, hn⟩ ∧
      (∀ j : Fin (n - 1),
        (u ⟨j.val, by omega⟩, xs ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
          POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
      0 ≤ u ⟨n - 1, by omega⟩ ∧ t ≤ u ⟨n - 1, by omega⟩ := by
  constructor
  · intro h
    refine ⟨prefixMean xs, prefixMean_first xs hn, prefixMean_mem xs hx,
      prefixMean_nonneg xs hx _, ?_⟩
    simpa only [prefixMean_last xs hn] using h
  · rintro ⟨u, hfirst, hchain, _, hbound⟩
    exact hbound.trans (chain_bound xs u hn hx hfirst hchain)

private theorem geoMean_neg_dimension {n : Nat} (xs : Fin n → ℝ) (hn : 0 < n)
    (hx : ∀ i, 0 ≤ xs i) :
    Fn.geoMean xs ^ (-(n : ℝ)) = Fn.invProd xs := by
  have hp : 0 ≤ ∏ i, xs i := Finset.prod_nonneg (fun i _ => hx i)
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hn)
  change ((∏ i, xs i) ^ (1 / (n : ℝ))) ^ (-(n : ℝ)) = (∏ i, xs i)⁻¹
  rw [← Real.rpow_mul hp]
  have hexp : 1 / (n : ℝ) * -(n : ℝ) = -1 := by field_simp
  rw [hexp, Real.rpow_neg_one]

/-- A nonempty inverse product gives a valid parameter for the final cone. -/
theorem invProdExponent_range (n : Nat) (hn : 0 < n) :
    0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) < 1 := by
  apply inverse_exponent_range
  exact_mod_cast Nat.lt_add_one_iff.mpr hn

/-- An inverse-product epigraph is the prefix-mean chain followed by one
negative-power cone. Strictly positive input coordinates are essential. -/
theorem invProd_le_iff {n : Nat} (xs : Fin n → ℝ) (t : ℝ) (hn : 0 < n)
    (hx : ∀ i, 0 < xs i) :
    Fn.invProd xs ≤ t ↔ ∃ u : Fin n → ℝ,
      u ⟨0, hn⟩ = xs ⟨0, hn⟩ ∧
      (∀ j : Fin (n - 1),
        (u ⟨j.val, by omega⟩, xs ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
          POW (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))) ∧
      (t, u ⟨n - 1, by omega⟩, 1) ∈ POW (1 / ((n : ℝ) + 1)) := by
  have hnℝ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnegative : -(n : ℝ) < 0 := neg_neg_of_pos hnℝ
  have hx₀ : ∀ i, 0 ≤ xs i := fun i => (hx i).le
  have hfinal (r : ℝ) (hr : 0 < r) :
      r ^ (-(n : ℝ)) ≤ t ↔ (t, r, 1) ∈ POW (1 / ((n : ℝ) + 1)) := by
    have hexp : 1 - -(n : ℝ) = (n : ℝ) + 1 := by ring
    simpa only [hexp] using rpow_neg_le_iff r t (-(n : ℝ)) hr hnegative
  constructor
  · intro h
    refine ⟨prefixMean xs, prefixMean_first xs hn, prefixMean_mem xs hx₀, ?_⟩
    rw [prefixMean_last xs hn]
    exact (hfinal _ (Fn.geoMean_pos xs hx)).mp ((geoMean_neg_dimension xs hn hx₀).symm ▸ h)
  · rintro ⟨u, hfirst, hchain, hcone⟩
    have hu : 0 < u ⟨n - 1, by omega⟩ := by
      have hu₀ := hcone.2.1
      apply lt_of_le_of_ne hu₀
      intro heq
      change 0 = u ⟨n - 1, by omega⟩ at heq
      have hcone₀ := hcone
      rw [← heq] at hcone₀
      have hzero := (Cone.mem_powerSet_zero_right _ _ _
        (invProdExponent_range n hn)).mp hcone₀
      norm_num at hzero
    have hpow := (hfinal _ hu).mpr hcone
    rw [← geoMean_neg_dimension xs hn hx₀]
    exact (Real.rpow_le_rpow_of_nonpos hu (chain_bound xs u hn hx₀ hfirst hchain)
      hnegative.le).trans hpow

/-- The unweighted finite geometric mean on nonnegative coordinates. The forward
witness sets auxiliary `i` to the mean of the first `i + 1` coordinates. -/
noncomputable def geoMeanHypograph {n : Nat} (hn : 0 < n) :
    HypographRepresentation (fun xs : {xs : Fin n → ℝ // ∀ i, 0 ≤ xs i} =>
      Fn.geoMean xs.1) where
  Auxiliary := Fin n → ℝ
  target xs t u :=
    u ⟨0, hn⟩ = xs.1 ⟨0, hn⟩ ∧
    (∀ j : Fin (n - 1),
      (u ⟨j.val, by omega⟩, xs.1 ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
        (Cone.power (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
          (prefixExponent_range j.val)).carrier) ∧
    0 ≤ u ⟨n - 1, by omega⟩ ∧ t ≤ u ⟨n - 1, by omega⟩
  source_iff_exists xs t := le_geoMean_iff xs.1 t hn xs.2

/-- The finite inverse product on strictly positive coordinates, using the
same prefix-mean layout and one final negative-power cone. -/
noncomputable def invProdEpigraph {n : Nat} (hn : 0 < n) :
    EpigraphRepresentation (fun xs : {xs : Fin n → ℝ // ∀ i, 0 < xs i} =>
      Fn.invProd xs.1) where
  Auxiliary := Fin n → ℝ
  target xs t u :=
    u ⟨0, hn⟩ = xs.1 ⟨0, hn⟩ ∧
    (∀ j : Fin (n - 1),
      (u ⟨j.val, by omega⟩, xs.1 ⟨j.val + 1, by omega⟩, u ⟨j.val + 1, by omega⟩) ∈
        (Cone.power (((j.val : ℝ) + 1) / ((j.val : ℝ) + 2))
          (prefixExponent_range j.val)).carrier) ∧
    (t, u ⟨n - 1, by omega⟩, 1) ∈
      (Cone.power (1 / ((n : ℝ) + 1)) (invProdExponent_range n hn)).carrier
  source_iff_exists xs t := invProd_le_iff xs.1 t hn xs.2

end Morew.Conic.Power
