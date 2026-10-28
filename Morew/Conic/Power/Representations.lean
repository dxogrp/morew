/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Basic
import Morew.Rewrite.Basic

/-!
# Exact scalar-power representations

Base domains are explicit subtype inputs. Real exponents remain exact parameters;
their range proofs determine the bundled power cone. Hypographs use a nonnegative
auxiliary above the original bound, so negative bounds remain feasible.

Native `Real.rpow` and canonical real-exponent notation have distinct registered
source patterns. The endpoint records require no sign condition on the base.
-/

namespace Morew.Conic.Power

/-- Convex positive powers on nonnegative bases. -/
noncomputable def rpowEpigraph (p : ℝ) (hp : 1 < p) :
    EpigraphRepresentation (fun x : {x : ℝ // 0 ≤ x} => Real.rpow x.1 p) where
  Auxiliary := Unit
  target x t _ := (t, 1, x.1) ∈ (Cone.power (1 / p) (inverse_exponent_range p hp)).carrier
  source_iff_exists x t := by
    change x.1 ^ p ≤ t ↔ ∃ _ : Unit, (t, 1, x.1) ∈ POW (1 / p)
    simpa only [exists_const] using rpow_le_iff x.1 t p x.2 hp

/-- Canonical real-power notation for convex positive powers. -/
noncomputable def rpowNotationEpigraph (p : ℝ) (hp : 1 < p) :
    EpigraphRepresentation (fun x : {x : ℝ // 0 ≤ x} => x.1 ^ p) :=
  rpowEpigraph p hp

/-- Convex negative powers on strictly positive bases. -/
noncomputable def rpowNegativeEpigraph (p : ℝ) (hp : p < 0) :
    EpigraphRepresentation (fun x : {x : ℝ // 0 < x} => Real.rpow x.1 p) where
  Auxiliary := Unit
  target x t _ := (t, x.1, 1) ∈
    (Cone.power (1 / (1 - p)) (negative_exponent_range p hp)).carrier
  source_iff_exists x t := by
    change x.1 ^ p ≤ t ↔ ∃ _ : Unit, (t, x.1, 1) ∈ POW (1 / (1 - p))
    simpa only [exists_const] using rpow_neg_le_iff x.1 t p x.2 hp

/-- Canonical real-power notation for convex negative powers. -/
noncomputable def rpowNegativeNotationEpigraph (p : ℝ) (hp : p < 0) :
    EpigraphRepresentation (fun x : {x : ℝ // 0 < x} => x.1 ^ p) :=
  rpowNegativeEpigraph p hp

/-- Concave fractional powers, including negative hypograph bounds. -/
noncomputable def rpowHypograph (p : ℝ) (hp : 0 < p ∧ p < 1) :
    HypographRepresentation (fun x : {x : ℝ // 0 ≤ x} => Real.rpow x.1 p) where
  Auxiliary := ℝ
  target x t u := 0 ≤ u ∧ t ≤ u ∧ (x.1, 1, u) ∈ (Cone.power p hp).carrier
  source_iff_exists x t := le_rpow_iff x.1 t p x.2 hp

/-- Canonical real-power notation for concave fractional powers. -/
noncomputable def rpowNotationHypograph (p : ℝ) (hp : 0 < p ∧ p < 1) :
    HypographRepresentation (fun x : {x : ℝ // 0 ≤ x} => x.1 ^ p) :=
  rpowHypograph p hp

/-- The binary weighted geometric mean on nonnegative inputs. -/
noncomputable def weightedGeoMeanHypograph (α : ℝ) (hα : 0 < α ∧ α < 1) :
    HypographRepresentation (fun x : {x : ℝ // 0 ≤ x} × {y : ℝ // 0 ≤ y} =>
      Real.rpow x.1.1 α * Real.rpow x.2.1 (1 - α)) where
  Auxiliary := ℝ
  target x t u := 0 ≤ u ∧ t ≤ u ∧ (x.1.1, x.2.1, u) ∈ (Cone.power α hα).carrier
  source_iff_exists x t := le_weightedGeomMean_iff x.1.1 x.2.1 t α x.1.2 x.2.2 hα

/-- Weighted geometric mean with notation for both powers. -/
noncomputable def weightedGeoMeanNotationHypograph (α : ℝ) (hα : 0 < α ∧ α < 1) :
    HypographRepresentation (fun x : {x : ℝ // 0 ≤ x} × {y : ℝ // 0 ≤ y} =>
      x.1.1 ^ α * x.2.1 ^ (1 - α)) := weightedGeoMeanHypograph α hα

/-- Weighted geometric mean with notation only for the left power. -/
noncomputable def weightedGeoMeanLeftNotationHypograph (α : ℝ) (hα : 0 < α ∧ α < 1) :
    HypographRepresentation (fun x : {x : ℝ // 0 ≤ x} × {y : ℝ // 0 ≤ y} =>
      x.1.1 ^ α * Real.rpow x.2.1 (1 - α)) := weightedGeoMeanHypograph α hα

/-- Weighted geometric mean with notation only for the right power. -/
noncomputable def weightedGeoMeanRightNotationHypograph (α : ℝ) (hα : 0 < α ∧ α < 1) :
    HypographRepresentation (fun x : {x : ℝ // 0 ≤ x} × {y : ℝ // 0 ≤ y} =>
      Real.rpow x.1.1 α * x.2.1 ^ (1 - α)) := weightedGeoMeanHypograph α hα

/-- The zeroth real power is the constant one on every real input. -/
noncomputable def rpowZeroEpigraph : EpigraphRepresentation (fun x : ℝ => Real.rpow x 0) where
  Auxiliary := Unit
  target _ t _ := 1 ≤ t
  source_iff_exists x t := by
    change x ^ (0 : ℝ) ≤ t ↔ ∃ _ : Unit, 1 ≤ t
    simp only [Real.rpow_zero, exists_const]

/-- The zeroth real power has the constant-one hypograph on every real input. -/
noncomputable def rpowZeroHypograph : HypographRepresentation (fun x : ℝ => Real.rpow x 0) where
  Auxiliary := Unit
  target _ t _ := t ≤ 1
  source_iff_exists x t := by
    change t ≤ x ^ (0 : ℝ) ↔ ∃ _ : Unit, t ≤ 1
    simp only [Real.rpow_zero, exists_const]

/-- The first real power has the unchanged epigraph on every real input. -/
noncomputable def rpowOneEpigraph : EpigraphRepresentation (fun x : ℝ => Real.rpow x 1) where
  Auxiliary := Unit
  target x t _ := x ≤ t
  source_iff_exists x t := by
    change x ^ (1 : ℝ) ≤ t ↔ ∃ _ : Unit, x ≤ t
    simp only [Real.rpow_one, exists_const]

/-- The first real power has the unchanged hypograph on every real input. -/
noncomputable def rpowOneHypograph : HypographRepresentation (fun x : ℝ => Real.rpow x 1) where
  Auxiliary := Unit
  target x t _ := t ≤ x
  source_iff_exists x t := by
    change t ≤ x ^ (1 : ℝ) ↔ ∃ _ : Unit, t ≤ x
    simp only [Real.rpow_one, exists_const]

/-- Notation spelling of the zeroth-power epigraph. -/
noncomputable def rpowZeroNotationEpigraph : EpigraphRepresentation (fun x : ℝ => x ^ (0 : ℝ)) :=
  rpowZeroEpigraph

/-- Notation spelling of the zeroth-power hypograph. -/
noncomputable def rpowZeroNotationHypograph : HypographRepresentation (fun x : ℝ => x ^ (0 : ℝ)) :=
  rpowZeroHypograph

/-- Notation spelling of the first-power epigraph. -/
noncomputable def rpowOneNotationEpigraph : EpigraphRepresentation (fun x : ℝ => x ^ (1 : ℝ)) :=
  rpowOneEpigraph

/-- Notation spelling of the first-power hypograph. -/
noncomputable def rpowOneNotationHypograph : HypographRepresentation (fun x : ℝ => x ^ (1 : ℝ)) :=
  rpowOneHypograph

end Morew.Conic.Power
