/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Basic
import Mathlib.Tactic.NormNum

/-!
# Power-cone semantics and exact scalar bounds

These checks cover cone laws at zero, both coordinate boundaries, signed last
coordinates, every supported exponent regime, and negative hypograph bounds.
They depend only on the semantic modules.
-/

assert_not_exists Morew.ExactConstraintLift Morew.Syntax.ProblemView

namespace MorewTest.Conic.Power

noncomputable section

open Morew.Conic

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (Cone.power α hα).Space = (ℝ × ℝ × ℝ) := rfl

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    NormedAddCommGroup (Cone.power α hα).Space := inferInstance

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    NormedSpace ℝ (Cone.power α hα).Space := inferInstance

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    FiniteDimensional ℝ (Cone.power α hα).Space := inferInstance

example (α : ℝ) : POW α = Cone.powerSet α := rfl

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (↑(Cone.power α hα).carrier : Set (Cone.power α hα).Space) = POW α := rfl

example (α x y z : ℝ) :
    (x, y, z) ∈ POW α ↔ 0 ≤ x ∧ 0 ≤ y ∧ |z| ≤ x ^ α * y ^ (1 - α) := by
  simp

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    (0 : ℝ × ℝ × ℝ) ∈ POW α := Cone.zero_mem_powerSet α hα

example (α y z : ℝ) (hα : 0 < α ∧ α < 1) :
    (0, y, z) ∈ POW α ↔ 0 ≤ y ∧ z = 0 :=
  Cone.mem_powerSet_zero_left α y z hα

example (α x z : ℝ) (hα : 0 < α ∧ α < 1) :
    (x, 0, z) ∈ POW α ↔ 0 ≤ x ∧ z = 0 :=
  Cone.mem_powerSet_zero_right α x z hα

example : ((1, 1, -1) : ℝ × ℝ × ℝ) ∈ POW (1 / 2) := by norm_num
example : ((1, 1, 1) : ℝ × ℝ × ℝ) ∈ POW (1 / 2) := by norm_num
example : ((-1, 1, 0) : ℝ × ℝ × ℝ) ∉ POW (1 / 2) := by norm_num
example : ((1, -1, 0) : ℝ × ℝ × ℝ) ∉ POW (1 / 2) := by norm_num
example : ((0, 1, 1) : ℝ × ℝ × ℝ) ∉ POW (1 / 2) := by norm_num
example : ((1, 0, -1) : ℝ × ℝ × ℝ) ∉ POW (1 / 2) := by norm_num

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    Convex ℝ (POW α) := Cone.convex_powerSet α hα

example (α : ℝ) (hα : 0 < α ∧ α < 1) :
    IsClosed (POW α) := Cone.isClosed_powerSet α hα

example (α : ℝ) (hα : 0 < α ∧ α < 1) (v w : ℝ × ℝ × ℝ)
    (hv : v ∈ POW α) (hw : w ∈ POW α) : v + w ∈ POW α :=
  (Cone.power α hα).carrier.add_mem hv hw

example (α : ℝ) (hα : 0 < α ∧ α < 1) (v : ℝ × ℝ × ℝ)
    (hv : v ∈ POW α) (c : ℝ) (hc : 0 ≤ c) : c • v ∈ POW α :=
  Cone.smul_mem_powerSet α hα c hc v hv

example (α : ℝ) (hα : 0 < α ∧ α < 1) (v : ℝ × ℝ × ℝ) :
    (0 : ℝ) • v ∈ POW α := by
  simpa using Cone.zero_mem_powerSet α hα

example (x t p : ℝ) (hx : 0 ≤ x) (hp : 1 < p) :
    x ^ p ≤ t ↔ (t, 1, x) ∈ POW (1 / p) :=
  Morew.Conic.Power.rpow_le_iff x t p hx hp

example (x t p : ℝ) (hx : 0 ≤ x) (hp : 0 < p ∧ p < 1) :
    t ≤ x ^ p ↔ ∃ u : ℝ, 0 ≤ u ∧ t ≤ u ∧ (x, 1, u) ∈ POW p :=
  Morew.Conic.Power.le_rpow_iff x t p hx hp

example (x t p : ℝ) (hx : 0 < x) (hp : p < 0) :
    x ^ p ≤ t ↔ (t, x, 1) ∈ POW (1 / (1 - p)) :=
  Morew.Conic.Power.rpow_neg_le_iff x t p hx hp

example (x y t α : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hα : 0 < α ∧ α < 1) :
    t ≤ x ^ α * y ^ (1 - α) ↔
      ∃ u : ℝ, 0 ≤ u ∧ t ≤ u ∧ (x, y, u) ∈ POW α :=
  Morew.Conic.Power.le_weightedGeomMean_iff x y t α hx hy hα

/-! Zero inputs are allowed for the positive-power epigraph and hypographs. -/

example : ((0, 1, 0) : ℝ × ℝ × ℝ) ∈ POW (1 / 3) := by norm_num

example : ∃ u : ℝ, 0 ≤ u ∧ -1 ≤ u ∧ (0, 1, u) ∈ POW (1 / 2) := by
  exact (Morew.Conic.Power.le_rpow_iff 0 (-1) (1 / 2) (by norm_num)
    (by norm_num)).mp (by norm_num)

/-! Direct cone membership would incorrectly discard this negative lower bound. -/

example : ((0, 1, -1) : ℝ × ℝ × ℝ) ∉ POW (1 / 2) := by norm_num

example : ∃ u : ℝ, 0 ≤ u ∧ -2 ≤ u ∧ (1, 0, u) ∈ POW (1 / 3) := by
  exact (Morew.Conic.Power.le_weightedGeomMean_iff 1 0 (-2) (1 / 3)
    (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num)

/-! Negative powers require positivity: totalized zero powers give a different epigraph. -/

example : (0 : ℝ) ^ (-1 : ℝ) ≤ 0 := by norm_num
example : ((0, 0, 1) : ℝ × ℝ × ℝ) ∉ POW (1 / (1 - (-1))) := by norm_num

/-! The two affine exponent boundaries retain native real-power semantics. -/

example (x t : ℝ) : x ^ (0 : ℝ) ≤ t ↔ 1 ≤ t := by simp
example (x t : ℝ) : t ≤ x ^ (0 : ℝ) ↔ t ≤ 1 := by simp
example (x t : ℝ) : x ^ (1 : ℝ) ≤ t ↔ x ≤ t := by simp
example (x t : ℝ) : t ≤ x ^ (1 : ℝ) ↔ t ≤ x := by simp

end

end MorewTest.Conic.Power
