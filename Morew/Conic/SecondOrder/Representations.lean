/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.SecondOrder
import Morew.Rewrite.Basic

/-!
# Exact second-order representations

These proof-bearing records expose the native operation in their source type.
Positive denominator domains are part of the input type; consumers must supply
checked domain evidence before using a quadratic-over-linear representation.
-/

namespace Morew.Conic.SecondOrder

/-- A Euclidean norm upper bound represented by one second-order cone row. -/
noncomputable def normEpigraph {n : Nat} :
    EpigraphRepresentation (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) where
  Auxiliary := Unit
  target z t _ := (t, WithLp.ofLp z) ∈ (Cone.secondOrder n).carrier
  source_iff_exists z t := by simpa only [exists_const] using norm_le_iff z t

/-- A squared Euclidean norm represented by a rotated cone. -/
noncomputable def normSquareEpigraph {n : Nat} :
    EpigraphRepresentation (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) where
  Auxiliary := Unit
  target z t _ := (t, 1 / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists z t := by simpa only [exists_const] using norm_sq_le_iff z t

/-- A full finite sum of coordinate squares represented by a rotated cone. -/
noncomputable def sumSquaresEpigraph {n : Nat} :
    EpigraphRepresentation (fun v : Fin n → ℝ => ∑ i, v i ^ 2) where
  Auxiliary := Unit
  target v t _ := (t, 1 / 2, fun i => v i) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists v t := by simpa only [exists_const] using sumSquares_le_iff v t

/-- A scalar square represented by a singleton rotated cone. -/
noncomputable def squareEpigraph : EpigraphRepresentation (fun a : ℝ => a ^ 2) where
  Auxiliary := Unit
  target a t _ := (t, 1 / 2, ![a]) ∈ (Cone.rotatedSecondOrder 1).carrier
  source_iff_exists a t := by simpa only [exists_const] using square_le_iff a t

/-- A positive-denominator squared Euclidean norm represented by a rotated cone. -/
noncomputable def normSquareDivEpigraph {n : Nat} :
    EpigraphRepresentation (fun p : EuclideanSpace ℝ (Fin n) × {y : ℝ // 0 < y} =>
      ‖p.1‖ ^ 2 / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, WithLp.ofLp p.1) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using norm_sq_div_le_iff p.1 p.2.1 t p.2.2

/-- A positive-denominator sum of squares represented by a rotated cone. -/
noncomputable def sumSquaresDivEpigraph {n : Nat} :
    EpigraphRepresentation (fun p : (Fin n → ℝ) × {y : ℝ // 0 < y} =>
      (∑ i, p.1 i ^ 2) / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, fun i => p.1 i) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using sumSquares_div_le_iff p.1 p.2.1 t p.2.2

/-- A positive-denominator scalar square represented by a rotated cone. -/
noncomputable def squareDivEpigraph :
    EpigraphRepresentation (fun p : ℝ × {y : ℝ // 0 < y} => p.1 ^ 2 / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, ![p.1]) ∈ (Cone.rotatedSecondOrder 1).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using square_div_le_iff p.1 p.2.1 t p.2.2

end Morew.Conic.SecondOrder
