/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.SecondOrder
import Morew.Rewrite.Basic
import Morew.Fn.Norm

/-!
# Exact second-order representations

These records represent Euclidean norms, squared norms, and quadratic-over-linear
expressions. Subtype inputs carry the positive denominator hypotheses.
-/

namespace Morew.Conic.SecondOrder

/-- A Euclidean norm upper bound represented by one second-order cone row. -/
noncomputable def normEpigraph {n : Nat} :
    EpigraphRepr (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) where
  Auxiliary := Unit
  target z t _ := (t, WithLp.ofLp z) ∈ (Cone.secondOrder n).carrier
  source_iff_exists z t := by simpa only [exists_const] using norm_le_iff z t

/-- The named Euclidean norm uses one second-order cone row on its input coordinates. -/
noncomputable def fnNorm2Epigraph {n : Nat} :
    EpigraphRepr (fun v : Fin n → ℝ => Fn.norm2 v) where
  Auxiliary := (normEpigraph (n := n)).Auxiliary
  target v t u := normEpigraph.target (WithLp.toLp 2 v) t u
  source_iff_exists v t :=
    normEpigraph.source_iff_exists (WithLp.toLp 2 v) t

/-- A squared Euclidean norm represented by a rotated cone. -/
noncomputable def normSquareEpigraph {n : Nat} :
    EpigraphRepr (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) where
  Auxiliary := Unit
  target z t _ := (t, 1 / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists z t := by simpa only [exists_const] using norm_sq_le_iff z t

/-- The squared named Euclidean norm uses one rotated cone row. -/
noncomputable def fnNorm2SquareEpigraph {n : Nat} :
    EpigraphRepr (fun v : Fin n → ℝ => Fn.norm2 v ^ 2) where
  Auxiliary := (normSquareEpigraph (n := n)).Auxiliary
  target v t u := normSquareEpigraph.target (WithLp.toLp 2 v) t u
  source_iff_exists v t :=
    normSquareEpigraph.source_iff_exists (WithLp.toLp 2 v) t

/-- A full finite sum of coordinate squares represented by a rotated cone. -/
noncomputable def sumSquaresEpigraph {n : Nat} :
    EpigraphRepr (fun v : Fin n → ℝ => ∑ i, v i ^ 2) where
  Auxiliary := Unit
  target v t _ := (t, 1 / 2, fun i => v i) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists v t := by simpa only [exists_const] using sumSquares_le_iff v t

/-- A scalar square represented by a singleton rotated cone. -/
noncomputable def squareEpigraph : EpigraphRepr (fun a : ℝ => a ^ 2) where
  Auxiliary := Unit
  target a t _ := (t, 1 / 2, ![a]) ∈ (Cone.rotatedSecondOrder 1).carrier
  source_iff_exists a t := by simpa only [exists_const] using square_le_iff a t

/-- A positive-denominator squared Euclidean norm represented by a rotated cone. -/
noncomputable def normSquareDivEpigraph {n : Nat} :
    EpigraphRepr (fun p : EuclideanSpace ℝ (Fin n) × {y : ℝ // 0 < y} =>
      ‖p.1‖ ^ 2 / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, WithLp.ofLp p.1) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using norm_sq_div_le_iff p.1 p.2.1 t p.2.2

/-- A positive-denominator sum of squares represented by a rotated cone. -/
noncomputable def sumSquaresDivEpigraph {n : Nat} :
    EpigraphRepr (fun p : (Fin n → ℝ) × {y : ℝ // 0 < y} =>
      (∑ i, p.1 i ^ 2) / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, fun i => p.1 i) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using sumSquares_div_le_iff p.1 p.2.1 t p.2.2

/-- A positive-denominator scalar square represented by a rotated cone. -/
noncomputable def squareDivEpigraph :
    EpigraphRepr (fun p : ℝ × {y : ℝ // 0 < y} => p.1 ^ 2 / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, ![p.1]) ∈ (Cone.rotatedSecondOrder 1).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using square_div_le_iff p.1 p.2.1 t p.2.2

end Morew.Conic.SecondOrder
