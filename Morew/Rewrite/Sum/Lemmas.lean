/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Exact finite-sum bounds

A bound on a finite sum is equivalent to bounds on its summands and one
inequality on the sum of the bounds. The index type may be empty.
-/

@[expose] public section

namespace Morew.Rewrite.Sum

/-- Compose exact scalar upper bounds into an upper bound on their finite sum. -/
theorem sum_le_iff_exists {I : Type*} [Fintype I]
    (f : I → ℝ) (R : I → ℝ → Prop)
    (hR : ∀ i s, f i ≤ s ↔ R i s) (t : ℝ) :
    (∑ i, f i) ≤ t ↔
      ∃ s : I → ℝ, (∀ i, R i (s i)) ∧ (∑ i, s i) ≤ t := by
  constructor
  · intro ht
    exact ⟨f, fun i => (hR i (f i)).mp le_rfl, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact (Finset.sum_le_sum fun i _ => (hR i (s i)).mpr (hs i)).trans ht

/-- Compose exact scalar lower bounds into a lower bound on their finite sum. -/
theorem le_sum_iff_exists {I : Type*} [Fintype I]
    (f : I → ℝ) (R : I → ℝ → Prop)
    (hR : ∀ i s, s ≤ f i ↔ R i s) (t : ℝ) :
    t ≤ (∑ i, f i) ↔
      ∃ s : I → ℝ, (∀ i, R i (s i)) ∧ t ≤ (∑ i, s i) := by
  constructor
  · intro ht
    exact ⟨f, fun i => (hR i (f i)).mp le_rfl, ht⟩
  · rintro ⟨s, hs, ht⟩
    exact ht.trans (Finset.sum_le_sum fun i _ => (hR i (s i)).mpr (hs i))

end Morew.Rewrite.Sum
