/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Fn.SumLargest
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp

/-!
# Empirical conditional value-at-risk

CVaR uses equally weighted finite losses and a real threshold infimum. Its
interpretation and exact linear epigraph require a nonempty sample and
`0 ≤ β < 1`. Fractional tail mass interpolates adjacent sums of largest losses.
-/

@[expose] public section

namespace Morew.Fn

open Finset

/-- Empirical CVaR for equally weighted losses, defined by the real threshold infimum.
Its interpretation and conic representation require `0 < n` and `0 ≤ β < 1`. -/
noncomputable def cvar {n : Nat} (β : ℝ) (x : Fin n → ℝ) : ℝ :=
  sInf (Set.range (fun τ : ℝ =>
    τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β))))

private theorem tailMass_pos {n : Nat} (β : ℝ) (hn : 0 < n)
    (hβ : 0 ≤ β ∧ β < 1) : 0 < (n : ℝ) * (1 - β) :=
  mul_pos (Nat.cast_pos.mpr hn) (sub_pos.mpr hβ.2)

private theorem interpolated_isLeast_threshold {n : Nat} (q : ℝ) (x : Fin n → ℝ)
    (k : Nat) (hk : k < n) (hkq : (k : ℝ) ≤ q) (hqk : q ≤ ((k + 1 : Nat) : ℝ)) :
    IsLeast (Set.range (fun τ : ℝ => q * τ + ∑ i, max (x i - τ) 0))
      ((((k + 1 : Nat) : ℝ) - q) * sumLargest k x +
        (q - (k : ℝ)) * sumLargest (k + 1) x) := by
  let α := q - (k : ℝ)
  have hα : 0 ≤ α := sub_nonneg.mpr hkq
  have hα' : 0 ≤ 1 - α := by dsimp [α]; push_cast at hqk; linarith
  have hinterp (τ : ℝ) :
      (1 - α) * ((k : ℝ) * τ + ∑ i, max (x i - τ) 0) +
        α * (((k + 1 : Nat) : ℝ) * τ + ∑ i, max (x i - τ) 0) =
      q * τ + ∑ i, max (x i - τ) 0 := by
    dsimp [α]
    push_cast
    ring
  have hcoeff : (((k + 1 : Nat) : ℝ) - q) = 1 - α := by dsimp [α]; push_cast; ring
  rw [hcoeff]
  obtain ⟨τ, hτ, hτ'⟩ := sumLargest_exists_common_threshold k x hk
  constructor
  · refine ⟨τ, ?_⟩
    rw [hτ, hτ']
    exact (hinterp τ).symm
  · rintro _ ⟨s, rfl⟩
    calc
      (1 - α) * sumLargest k x + α * sumLargest (k + 1) x ≤
          (1 - α) * ((k : ℝ) * s + ∑ i, max (x i - s) 0) +
            α * (((k + 1 : Nat) : ℝ) * s + ∑ i, max (x i - s) 0) :=
        add_le_add (mul_le_mul_of_nonneg_left (sumLargest_le_threshold k x s hk.le) hα')
          (mul_le_mul_of_nonneg_left (sumLargest_le_threshold (k + 1) x s hk) hα)
      _ = _ := hinterp s

private theorem exists_isLeast_threshold {n : Nat} (q : ℝ) (x : Fin n → ℝ)
    (hq : 0 < q) (hqn : q ≤ (n : ℝ)) :
    ∃ v : ℝ, IsLeast (Set.range (fun τ : ℝ => q * τ + ∑ i, max (x i - τ) 0)) v := by
  rcases lt_or_eq_of_le hqn with hqn | rfl
  · let k := Nat.floor q
    have hk : k < n := (Nat.floor_lt hq.le).mpr hqn
    have hkq : (k : ℝ) ≤ q := Nat.floor_le hq.le
    have hqk : q ≤ ((k + 1 : Nat) : ℝ) := by
      exact_mod_cast (Nat.lt_floor_add_one q).le
    exact ⟨_, interpolated_isLeast_threshold q x k hk hkq hqk⟩
  · exact ⟨sumLargest n x, sumLargest_isLeast_threshold n x (le_refl n)⟩

private theorem scaled_isLeast_threshold {n : Nat} (q : ℝ) (x : Fin n → ℝ)
    (hq : 0 < q) (v : ℝ)
    (hv : IsLeast (Set.range (fun τ : ℝ => q * τ + ∑ i, max (x i - τ) 0)) v) :
    IsLeast (Set.range (fun τ : ℝ => τ + (∑ i, max (x i - τ) 0) / q)) (v / q) := by
  have hscale (τ : ℝ) : τ + (∑ i, max (x i - τ) 0) / q =
      (q * τ + ∑ i, max (x i - τ) 0) / q := by
    field_simp
  constructor
  · obtain ⟨τ, hτ⟩ := hv.1
    exact ⟨τ, (hscale τ).trans (congrArg (· / q) hτ)⟩
  · rintro _ ⟨τ, rfl⟩
    change v / q ≤ τ + (∑ i, max (x i - τ) 0) / q
    rw [hscale]
    exact div_le_div_of_nonneg_right (hv.2 ⟨τ, rfl⟩) hq.le

/-- On its certified domain, CVaR is the attained minimum of the threshold objective. -/
theorem cvar_isLeast_threshold {n : Nat} (β : ℝ) (x : Fin n → ℝ)
    (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) :
    IsLeast (Set.range (fun τ : ℝ =>
      τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β)))) (cvar β x) := by
  have hq := tailMass_pos β hn hβ
  have hqn : (n : ℝ) * (1 - β) ≤ n := by
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  obtain ⟨v, hv⟩ := exists_isLeast_threshold ((n : ℝ) * (1 - β)) x hq hqn
  have hleast := scaled_isLeast_threshold ((n : ℝ) * (1 - β)) x hq v hv
  change IsLeast _ (sInf _)
  rw [hleast.csInf_eq]
  exact hleast

/-- The certified threshold objective is bounded below. -/
theorem cvar_bddBelow_threshold {n : Nat} (β : ℝ) (x : Fin n → ℝ)
    (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) :
    BddBelow (Set.range (fun τ : ℝ =>
      τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β)))) :=
  ⟨cvar β x, (cvar_isLeast_threshold β x hn hβ).2⟩

/-- A real threshold attains CVaR on the certified domain. -/
theorem cvar_exists_threshold {n : Nat} (β : ℝ) (x : Fin n → ℝ)
    (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) :
    ∃ τ : ℝ, cvar β x =
      τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β)) := by
  obtain ⟨τ, hτ⟩ := (cvar_isLeast_threshold β x hn hβ).1
  exact ⟨τ, hτ.symm⟩

/-- Every threshold gives an upper bound on CVaR. -/
theorem cvar_le_threshold {n : Nat} (β : ℝ) (x : Fin n → ℝ) (τ : ℝ)
    (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) :
    cvar β x ≤ τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β)) :=
  (cvar_isLeast_threshold β x hn hβ).2 ⟨τ, rfl⟩

/-- An exact linear epigraph with a threshold and nonnegative excess variables. -/
theorem cvar_le_iff {n : Nat} (β : ℝ) (x : Fin n → ℝ) (t : ℝ)
    (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) :
    cvar β x ≤ t ↔ ∃ τ : ℝ, ∃ u : Fin n → ℝ,
      (∀ i, 0 ≤ u i) ∧ (∀ i, x i - τ ≤ u i) ∧
        τ + (∑ i, u i) / ((n : ℝ) * (1 - β)) ≤ t := by
  constructor
  · intro ht
    obtain ⟨τ, hτ⟩ := cvar_exists_threshold β x hn hβ
    refine ⟨τ, fun i => max (x i - τ) 0, fun _ => le_max_right _ _,
      fun _ => le_max_left _ _, ?_⟩
    exact hτ.symm.le.trans ht
  · rintro ⟨τ, u, hu, hx, ht⟩
    calc
      cvar β x ≤ τ + (∑ i, max (x i - τ) 0) / ((n : ℝ) * (1 - β)) :=
        cvar_le_threshold β x τ hn hβ
      _ ≤ τ + (∑ i, u i) / ((n : ℝ) * (1 - β)) :=
        add_le_add le_rfl (div_le_div_of_nonneg_right
          (sum_le_sum fun i _ => max_le (hx i) (hu i)) (tailMass_pos β hn hβ).le)
      _ ≤ t := ht

/-- Integer tail mass gives the average of the largest `k` losses. -/
theorem cvar_eq_sumLargest_div {n : Nat} (β : ℝ) (x : Fin n → ℝ) (k : Nat)
    (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) (hk : 1 ≤ k ∧ k ≤ n)
    (hq : (n : ℝ) * (1 - β) = (k : ℝ)) :
    cvar β x = sumLargest k x / (k : ℝ) := by
  have hleast : IsLeast
      (Set.range (fun τ : ℝ => (n : ℝ) * (1 - β) * τ + ∑ i, max (x i - τ) 0))
      (sumLargest k x) := by
    rw [hq]
    exact sumLargest_isLeast_threshold k x hk.2
  have hscaled := scaled_isLeast_threshold ((n : ℝ) * (1 - β)) x
    (tailMass_pos β hn hβ) (sumLargest k x) hleast
  exact hscaled.csInf_eq.trans (by rw [hq])

/-- At confidence level zero, CVaR is the sample mean. -/
theorem cvar_zero {n : Nat} (x : Fin n → ℝ) (hn : 0 < n) :
    cvar 0 x = (∑ i, x i) / (n : ℝ) := by
  simpa only [sub_zero, mul_one, sumLargest_of_le n x (le_refl n)] using
    cvar_eq_sumLargest_div 0 x n hn ⟨le_rfl, zero_lt_one⟩ ⟨hn, le_rfl⟩ (by simp)

/-- Fractional tail mass interpolates adjacent sums of the largest losses. -/
theorem cvar_eq_interpolate_sumLargest {n : Nat} (β : ℝ) (x : Fin n → ℝ) (k : Nat)
    (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) (hk : k < n)
    (hkq : (k : ℝ) ≤ (n : ℝ) * (1 - β))
    (hqk : (n : ℝ) * (1 - β) ≤ ((k + 1 : Nat) : ℝ)) :
    cvar β x =
      ((((k + 1 : Nat) : ℝ) - (n : ℝ) * (1 - β)) * sumLargest k x +
        ((n : ℝ) * (1 - β) - (k : ℝ)) * sumLargest (k + 1) x) /
          ((n : ℝ) * (1 - β)) :=
  (scaled_isLeast_threshold ((n : ℝ) * (1 - β)) x (tailMass_pos β hn hβ) _
    (interpolated_isLeast_threshold ((n : ℝ) * (1 - β)) x k hk hkq hqk)).csInf_eq

end Morew.Fn
