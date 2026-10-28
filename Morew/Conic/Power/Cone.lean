/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Cone
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Three-dimensional power cones

Power cones use ordinary right-associated triples `(x, y, z)`, with nonnegative
first and second coordinates and `|z| ≤ x ^ α * y ^ (1 - α)`. The raw set is
available for every real parameter; its bundled cone and cone laws require
`0 < α ∧ α < 1`. The definition includes both zero-coordinate boundaries.
-/

namespace Morew.Conic.Cone

/-- The power-cone predicate, available independently of a parameter certificate. -/
noncomputable def powerSet (α : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ |p.2.2| ≤ p.1 ^ α * p.2.1 ^ (1 - α)}

/-- Power-set membership in ordinary coordinates. -/
@[simp]
theorem mem_powerSet (α x y z : ℝ) :
    (x, y, z) ∈ powerSet α ↔
      0 ≤ x ∧ 0 ≤ y ∧ |z| ≤ x ^ α * y ^ (1 - α) :=
  Iff.rfl

private theorem weighted_product_add_le (α : ℝ) (hα : 0 < α ∧ α < 1)
    (x₁ x₂ y₁ y₂ : ℝ) (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hy₁ : 0 ≤ y₁) (hy₂ : 0 ≤ y₂) :
    x₁ ^ α * y₁ ^ (1 - α) + x₂ ^ α * y₂ ^ (1 - α) ≤
      (x₁ + x₂) ^ α * (y₁ + y₂) ^ (1 - α) := by
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ ![x₁ ^ α, x₂ ^ α] i := by
    intro i _
    fin_cases i <;> exact Real.rpow_nonneg (by assumption) _
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      0 ≤ ![y₁ ^ (1 - α), y₂ ^ (1 - α)] i := by
    intro i _
    fin_cases i <;> exact Real.rpow_nonneg (by assumption) _
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ
    (Real.HolderConjugate.inv_one_sub_inv hα.1 hα.2) hf hg
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.rpow_rpow_inv hx₁ hα.1.ne', Real.rpow_rpow_inv hx₂ hα.1.ne',
    Real.rpow_rpow_inv hy₁ (sub_pos.mpr hα.2).ne',
    Real.rpow_rpow_inv hy₂ (sub_pos.mpr hα.2).ne', one_div, inv_inv] using h

private theorem weighted_product_smul (α c x y : ℝ) (hα : 0 < α ∧ α < 1)
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (c * x) ^ α * (c * y) ^ (1 - α) = c * (x ^ α * y ^ (1 - α)) := by
  rw [Real.mul_rpow hc hx, Real.mul_rpow hc hy]
  have hsum : c ^ α * c ^ (1 - α) = c := by
    rw [← Real.rpow_add_of_nonneg hc hα.1.le (sub_nonneg.mpr hα.2.le)]
    simp
  calc
    c ^ α * x ^ α * (c ^ (1 - α) * y ^ (1 - α))
        = (c ^ α * c ^ (1 - α)) * (x ^ α * y ^ (1 - α)) := by ring
    _ = _ := by rw [hsum]

/-- The power set is closed under nonnegative scaling, including scale zero. -/
theorem smul_mem_powerSet (α : ℝ) (hα : 0 < α ∧ α < 1)
    (c : ℝ) (hc : 0 ≤ c) (p : ℝ × ℝ × ℝ) (hp : p ∈ powerSet α) :
    c • p ∈ powerSet α := by
  obtain ⟨hx, hy, hz⟩ := hp
  change 0 ≤ c * p.1 ∧ 0 ≤ c * p.2.1 ∧
    |c * p.2.2| ≤ (c * p.1) ^ α * (c * p.2.1) ^ (1 - α)
  refine ⟨mul_nonneg hc hx, mul_nonneg hc hy, ?_⟩
  rw [abs_mul, abs_of_nonneg hc, weighted_product_smul α c p.1 p.2.1 hα hc hx hy]
  exact mul_le_mul_of_nonneg_left hz hc

/-- The power set is closed under addition, also when leading coordinates vanish. -/
theorem add_mem_powerSet (α : ℝ) (hα : 0 < α ∧ α < 1)
    (p q : ℝ × ℝ × ℝ) (hp : p ∈ powerSet α) (hq : q ∈ powerSet α) :
    p + q ∈ powerSet α := by
  obtain ⟨hpx, hpy, hpz⟩ := hp
  obtain ⟨hqx, hqy, hqz⟩ := hq
  refine ⟨add_nonneg hpx hqx, add_nonneg hpy hqy, ?_⟩
  exact (abs_add_le _ _).trans ((add_le_add hpz hqz).trans
    (weighted_product_add_le α hα p.1 q.1 p.2.1 q.2.1 hpx hqx hpy hqy))

/-- A closed convex power cone with a checked parameter in `(0, 1)`. -/
noncomputable def power (α : ℝ) (hα : 0 < α ∧ α < 1) : Cone where
  Space := ℝ × ℝ × ℝ
  carrier := {
    carrier := powerSet α
    smul_mem' := fun c hc p hp => smul_mem_powerSet α hα c hc.le p hp
    add_mem' := fun p hp q hq => add_mem_powerSet α hα p q hp hq }

/-- The bundled power cone has exactly the raw power-set carrier. -/
@[simp]
theorem mem_power (α : ℝ) (hα : 0 < α ∧ α < 1) (p : ℝ × ℝ × ℝ) :
    p ∈ (power α hα).carrier ↔ p ∈ powerSet α :=
  Iff.rfl

/-- The origin belongs to every power cone with a valid parameter. -/
@[simp]
theorem zero_mem_powerSet (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (0 : ℝ × ℝ × ℝ) ∈ powerSet α := by
  simp [powerSet, Real.zero_rpow hα.1.ne']

/-- A zero first coordinate forces the last coordinate to vanish. -/
theorem mem_powerSet_zero_left (α y z : ℝ) (hα : 0 < α ∧ α < 1) :
    (0, y, z) ∈ powerSet α ↔ 0 ≤ y ∧ z = 0 := by
  simp [Real.zero_rpow hα.1.ne']

/-- A zero second coordinate forces the last coordinate to vanish. -/
theorem mem_powerSet_zero_right (α x z : ℝ) (hα : 0 < α ∧ α < 1) :
    (x, 0, z) ∈ powerSet α ↔ 0 ≤ x ∧ z = 0 := by
  simp [Real.zero_rpow (sub_pos.mpr hα.2).ne']

/-- Power cones are convex with their zero-coordinate boundaries included. -/
theorem convex_powerSet (α : ℝ) (hα : 0 < α ∧ α < 1) :
    Convex ℝ (powerSet α) :=
  (power α hα).carrier.convex

/-- Power cones are closed, since both powers have positive exponents. -/
theorem isClosed_powerSet (α : ℝ) (hα : 0 < α ∧ α < 1) :
    IsClosed (powerSet α) := by
  have hx : Continuous (fun p : ℝ × ℝ × ℝ => p.1 ^ α) :=
    (Real.continuous_rpow_const hα.1.le).comp continuous_fst
  have hy : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1 ^ (1 - α)) :=
    (Real.continuous_rpow_const (sub_nonneg.mpr hα.2.le)).comp
      (continuous_fst.comp continuous_snd)
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const (continuous_fst.comp continuous_snd)).inter
      (isClosed_le (continuous_snd.comp continuous_snd).abs (hx.mul hy)))

/-- The checked power cone has a closed carrier. -/
theorem isClosed_power (α : ℝ) (hα : 0 < α ∧ α < 1) :
    IsClosed (↑(power α hα).carrier : Set (power α hα).Space) :=
  isClosed_powerSet α hα

end Morew.Conic.Cone

namespace Morew.Conic

set_option quotPrecheck false in
/-- The raw power-cone set. Conic classification separately checks `0 < α < 1`. -/
notation:max (name := powerCarrier) "POW " α:arg => Morew.Conic.Cone.powerSet α

end Morew.Conic
