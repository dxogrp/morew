/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sum of the largest coordinates

The sum of the largest `k` coordinates of a finite real vector uses every
coordinate when `k` exceeds its dimension. For `k` at most the dimension, an
attained threshold formula gives an exact linear epigraph.
-/

namespace Morew.Fn

open Finset

/-- The sum of the first `min k n` coordinates in nonincreasing order. -/
noncomputable def sumLargest {n : Nat} (k : Nat) (x : Fin n → ℝ) : ℝ :=
  ∑ i with i.val < k, x (Tuple.sort (OrderDual.toDual ∘ x) i)

/-- Selecting no coordinates gives zero. -/
@[simp] theorem sumLargest_zero_left {n : Nat} (x : Fin n → ℝ) :
    sumLargest 0 x = 0 := by
  simp [sumLargest]

/-- Every selection from an empty vector gives zero. -/
@[simp] theorem sumLargest_empty (k : Nat) (x : Fin 0 → ℝ) :
    sumLargest k x = 0 := by
  simp [sumLargest]

/-- Selecting at least the dimension gives the sum of all coordinates. -/
theorem sumLargest_of_le {n : Nat} (k : Nat) (x : Fin n → ℝ) (hnk : n ≤ k) :
    sumLargest k x = ∑ i, x i := by
  have hfilter : univ.filter (fun i : Fin n => i.val < k) = univ := by
    apply filter_eq_self.mpr
    intro i _
    exact i.isLt.trans_le hnk
  rw [sumLargest, hfilter]
  exact Equiv.sum_comp (Tuple.sort (OrderDual.toDual ∘ x)) x

/-- Sorting does not change a vector that is already nonincreasing. -/
theorem sumLargest_eq_sum_of_antitone {n : Nat} (k : Nat) (x : Fin n → ℝ)
    (hx : Antitone x) : sumLargest k x = ∑ i with i.val < k, x i := by
  have hsort : Tuple.sort (OrderDual.toDual ∘ x) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr hx
  simp only [sumLargest, hsort, Equiv.refl_apply]

/-- Permuting the input coordinates preserves the sum of the largest ones. -/
theorem sumLargest_comp_perm {n : Nat} (k : Nat) (x : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) : sumLargest k (x ∘ σ) = sumLargest k x := by
  have hsort := Tuple.comp_perm_comp_sort_eq_comp_sort
    (f := OrderDual.toDual ∘ x) (σ := σ)
  unfold sumLargest
  apply sum_congr rfl
  intro i _
  exact congrFun hsort i

/-- In positive dimension, selecting one coordinate gives the maximum. -/
theorem sumLargest_one {n : Nat} (x : Fin n → ℝ) (hn : 0 < n) :
    sumLargest 1 x = univ.sup' ⟨⟨0, hn⟩, mem_univ _⟩ x := by
  let σ := Tuple.sort (OrderDual.toDual ∘ x)
  have hy : Antitone (x ∘ σ) := Tuple.monotone_sort (OrderDual.toDual ∘ x)
  have hfilter : univ.filter (fun i : Fin n => i.val < 1) = {⟨0, hn⟩} := by
    ext i
    simp [Nat.lt_one_iff, Fin.ext_iff]
  rw [sumLargest, hfilter, sum_singleton]
  apply le_antisymm
  · exact le_sup' x (mem_univ _)
  · apply sup'_le
    intro i _
    have hi := hy (show (⟨0, hn⟩ : Fin n) ≤ σ.symm i from Nat.zero_le _)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi

private theorem card_prefix {n : Nat} (k : Nat) (hk : k ≤ n) :
    (univ.filter (fun i : Fin n => i.val < k)).card = k := by
  rcases lt_or_eq_of_le hk with hkn | hkn
  · have hfilter : univ.filter (fun i : Fin n => i.val < k) = Iio ⟨k, hkn⟩ := by
      ext i
      simp [Fin.lt_def]
    rw [hfilter, Fin.card_Iio]
  · subst k
    have hfilter : univ.filter (fun i : Fin n => i.val < n) = univ := by
      simp
    rw [hfilter, card_fin]

/-- Every threshold gives an upper bound on the sum of the largest coordinates. -/
theorem sumLargest_le_threshold {n : Nat} (k : Nat) (x : Fin n → ℝ) (τ : ℝ)
    (hk : k ≤ n) :
    sumLargest k x ≤ (k : ℝ) * τ + ∑ i, max (x i - τ) 0 := by
  let σ := Tuple.sort (OrderDual.toDual ∘ x)
  let s := univ.filter (fun i : Fin n => i.val < k)
  have hcard : s.card = k := card_prefix k hk
  have hprefix : ∑ i ∈ s, (x (σ i) - τ) ≤ ∑ i, max (x (σ i) - τ) 0 := by
    calc
      ∑ i ∈ s, (x (σ i) - τ) ≤ ∑ i ∈ s, max (x (σ i) - τ) 0 :=
        sum_le_sum fun _ _ => le_max_left _ _
      _ ≤ ∑ i, max (x (σ i) - τ) 0 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => le_max_right _ _)
  rw [sum_sub_distrib, sum_const, hcard, nsmul_eq_mul] at hprefix
  have hsum : (∑ i, max (x (σ i) - τ) 0) = ∑ i, max (x i - τ) 0 :=
    Equiv.sum_comp σ (fun i => max (x i - τ) 0)
  rw [hsum] at hprefix
  change (∑ i ∈ s, x (σ i)) ≤ _
  linarith

private theorem prefix_eq_threshold {n : Nat} (k : Nat) (x : Fin n → ℝ) (τ : ℝ)
    (hk : k ≤ n) (hl : ∀ i, i.val < k → τ ≤ x i)
    (hu : ∀ i, k ≤ i.val → x i ≤ τ) :
    (∑ i with i.val < k, x i) = (k : ℝ) * τ + ∑ i, max (x i - τ) 0 := by
  have hsum : (∑ i, max (x i - τ) 0) = ∑ i with i.val < k, (x i - τ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    by_cases hi : i.val < k
    · rw [ite_eq_left hi, max_eq_left (sub_nonneg.mpr (hl i hi))]
    · rw [ite_eq_right hi, max_eq_right (sub_nonpos.mpr (hu i (Nat.le_of_not_gt hi)))]
  rw [hsum, sum_sub_distrib, sum_const, card_prefix k hk, nsmul_eq_mul]
  ring

/-- A threshold between the selected and remaining coordinates attains the bound. -/
theorem sumLargest_exists_threshold {n : Nat} (k : Nat) (x : Fin n → ℝ)
    (hk : k ≤ n) :
    ∃ τ : ℝ, sumLargest k x = (k : ℝ) * τ + ∑ i, max (x i - τ) 0 := by
  by_cases hn : n = 0
  · subst n
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact ⟨0, by simp⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let σ := Tuple.sort (OrderDual.toDual ∘ x)
  let y := x ∘ σ
  have hy : Antitone y := Tuple.monotone_sort (OrderDual.toDual ∘ x)
  have hτ : ∃ τ : ℝ, (∀ i, i.val < k → τ ≤ y i) ∧
      (∀ i, k ≤ i.val → y i ≤ τ) := by
    by_cases hkn : k < n
    · refine ⟨y ⟨k, hkn⟩, ?_, ?_⟩
      · intro i hi
        exact hy (show i ≤ ⟨k, hkn⟩ from hi.le)
      · intro i hi
        exact hy (show (⟨k, hkn⟩ : Fin n) ≤ i from hi)
    · have hkn' : k = n := Nat.le_antisymm hk (Nat.le_of_not_gt hkn)
      let j : Fin n := ⟨n - 1, Nat.sub_lt hnpos (by decide)⟩
      refine ⟨y j, ?_, ?_⟩
      · intro i _
        exact hy (show i ≤ j from Nat.le_sub_one_of_lt i.isLt)
      · intro i hi
        exact (Nat.not_le_of_lt i.isLt (hkn' ▸ hi)).elim
  obtain ⟨τ, hl, hu⟩ := hτ
  refine ⟨τ, ?_⟩
  calc
    sumLargest k x = (k : ℝ) * τ + ∑ i, max (y i - τ) 0 :=
      prefix_eq_threshold k y τ hk hl hu
    _ = (k : ℝ) * τ + ∑ i, max (x i - τ) 0 := by
      rw [show (∑ i, max (y i - τ) 0) = ∑ i, max (x i - τ) 0 from
        Equiv.sum_comp σ (fun i => max (x i - τ) 0)]

/-- The threshold formula has a minimum equal to the sum of the largest coordinates. -/
theorem sumLargest_isLeast_threshold {n : Nat} (k : Nat) (x : Fin n → ℝ)
    (hk : k ≤ n) :
    IsLeast (Set.range (fun τ : ℝ => (k : ℝ) * τ + ∑ i, max (x i - τ) 0))
      (sumLargest k x) := by
  obtain ⟨τ, hτ⟩ := sumLargest_exists_threshold k x hk
  refine ⟨⟨τ, hτ.symm⟩, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact sumLargest_le_threshold k x s hk

/-- A sorted coordinate attains the threshold bounds for two adjacent selections. -/
theorem sumLargest_exists_common_threshold {n : Nat} (k : Nat) (x : Fin n → ℝ)
    (hk : k < n) :
    ∃ τ : ℝ,
      sumLargest k x = (k : ℝ) * τ + ∑ i, max (x i - τ) 0 ∧
      sumLargest (k + 1) x = ((k + 1 : Nat) : ℝ) * τ + ∑ i, max (x i - τ) 0 := by
  let σ := Tuple.sort (OrderDual.toDual ∘ x)
  let y := x ∘ σ
  have hy : Antitone y := Tuple.monotone_sort (OrderDual.toDual ∘ x)
  let τ := y ⟨k, hk⟩
  have hsum : (∑ i, max (y i - τ) 0) = ∑ i, max (x i - τ) 0 :=
    Equiv.sum_comp σ (fun i => max (x i - τ) 0)
  refine ⟨τ, ?_, ?_⟩
  · calc
      sumLargest k x = (k : ℝ) * τ + ∑ i, max (y i - τ) 0 :=
        prefix_eq_threshold k y τ hk.le
          (fun i hi => hy (show i ≤ ⟨k, hk⟩ from hi.le))
          (fun i hi => hy (show (⟨k, hk⟩ : Fin n) ≤ i from hi))
      _ = _ := by rw [hsum]
  · calc
      sumLargest (k + 1) x = ((k + 1 : Nat) : ℝ) * τ + ∑ i, max (y i - τ) 0 :=
        prefix_eq_threshold (k + 1) y τ hk
          (fun i hi => hy (show i ≤ ⟨k, hk⟩ from Nat.le_of_lt_succ hi))
          (fun i hi => hy (show (⟨k, hk⟩ : Fin n) ≤ i from (Nat.le_succ k).trans hi))
      _ = _ := by rw [hsum]

/-- An exact linear epigraph with a threshold and nonnegative excess variables. -/
theorem sumLargest_le_iff {n : Nat} (k : Nat) (x : Fin n → ℝ) (t : ℝ)
    (hk : k ≤ n) :
    sumLargest k x ≤ t ↔ ∃ τ : ℝ, ∃ u : Fin n → ℝ,
      (∀ i, 0 ≤ u i) ∧ (∀ i, x i - τ ≤ u i) ∧ (k : ℝ) * τ + ∑ i, u i ≤ t := by
  constructor
  · intro ht
    obtain ⟨τ, hτ⟩ := sumLargest_exists_threshold k x hk
    refine ⟨τ, fun i => max (x i - τ) 0, fun _ => le_max_right _ _,
      fun _ => le_max_left _ _, ?_⟩
    exact hτ.symm.le.trans ht
  · rintro ⟨τ, u, hu, hx, ht⟩
    calc
      sumLargest k x ≤ (k : ℝ) * τ + ∑ i, max (x i - τ) 0 :=
        sumLargest_le_threshold k x τ hk
      _ ≤ (k : ℝ) * τ + ∑ i, u i := by
        exact add_le_add le_rfl (sum_le_sum fun i _ => max_le (hx i) (hu i))
      _ ≤ t := ht

end Morew.Fn
