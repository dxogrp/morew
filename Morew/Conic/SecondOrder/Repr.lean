/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.SecondOrder
import Morew.Rewrite.Basic
import Morew.Fn.Norm

/-!
# Exact second-order representations

These records represent Euclidean norms, squared norms, Huber loss, and
quadratic-over-linear expressions. Subtype inputs carry the positive denominator
hypotheses. The Huber threshold is a fixed nonnegative parameter.
-/

namespace Morew.Conic.SecondOrder

/-- A Euclidean norm upper bound represented by one second-order cone row. -/
def normEpigraph {n : Nat} :
    EpigraphRepr (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) where
  Auxiliary := Unit
  target z t _ := (t, WithLp.ofLp z) ∈ (Cone.secondOrder n).carrier
  source_iff_exists z t := by simpa only [exists_const] using norm_le_iff z t

/-- The named Euclidean norm uses one second-order cone row on its input coordinates. -/
def fnNorm2Epigraph {n : Nat} :
    EpigraphRepr (fun v : Fin n → ℝ => Fn.norm2 v) where
  Auxiliary := (normEpigraph (n := n)).Auxiliary
  target v t u := normEpigraph.target (WithLp.toLp 2 v) t u
  source_iff_exists v t :=
    normEpigraph.source_iff_exists (WithLp.toLp 2 v) t

/-- A squared Euclidean norm represented by a rotated cone. -/
def normSquareEpigraph {n : Nat} :
    EpigraphRepr (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) where
  Auxiliary := Unit
  target z t _ := (t, 1 / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists z t := by simpa only [exists_const] using norm_sq_le_iff z t

/-- The squared named Euclidean norm uses one rotated cone row. -/
def fnNorm2SquareEpigraph {n : Nat} :
    EpigraphRepr (fun v : Fin n → ℝ => Fn.norm2 v ^ 2) where
  Auxiliary := (normSquareEpigraph (n := n)).Auxiliary
  target v t u := normSquareEpigraph.target (WithLp.toLp 2 v) t u
  source_iff_exists v t :=
    normSquareEpigraph.source_iff_exists (WithLp.toLp 2 v) t

/-- A full finite sum of coordinate squares represented by a rotated cone. -/
def sumSquaresEpigraph {n : Nat} :
    EpigraphRepr (fun v : Fin n → ℝ => ∑ i, v i ^ 2) where
  Auxiliary := Unit
  target v t _ := (t, 1 / 2, fun i => v i) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists v t := by simpa only [exists_const] using sumSquares_le_iff v t

/-- A scalar square represented by a singleton rotated cone. -/
def squareEpigraph : EpigraphRepr (fun a : ℝ => a ^ 2) where
  Auxiliary := Unit
  target a t _ := (t, 1 / 2, ![a]) ∈ (Cone.rotatedSecondOrder 1).carrier
  source_iff_exists a t := by simpa only [exists_const] using square_le_iff a t

/-- Huber loss represented by one rotated cone and three linear inequalities. -/
def huberEpigraph (M : ℝ) (hM : 0 ≤ M) : EpigraphRepr (Fn.huber M) where
  Auxiliary := ℝ × ℝ × ℝ
  target x t a := (a.2.1, 1 / 2, ![a.1]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
    -a.2.2 ≤ x - a.1 ∧ x - a.1 ≤ a.2.2 ∧ a.2.1 + 2 * M * a.2.2 ≤ t
  source_iff_exists x t := by
    simpa only [Prod.exists] using huber_le_iff M x t hM

/-- A finite Huber sum represented by one rotated cone and two vector bounds. -/
def sumHuberEpigraph {n : Nat} (M : ℝ) (hM : 0 ≤ M) :
    EpigraphRepr (fun v : Fin n → ℝ => ∑ i, Fn.huber M (v i)) where
  Auxiliary := (Fin n → ℝ) × (Fin n → ℝ)
  target v t a := (t - 2 * M * (∑ i, a.2 i), 1 / 2, a.1) ∈
      (Cone.rotatedSecondOrder n).carrier ∧ -a.2 ≤ v - a.1 ∧ v - a.1 ≤ a.2
  source_iff_exists v t := by
    simpa only [Prod.exists] using sum_huber_le_iff M v t hM

/-- A positive-denominator squared Euclidean norm represented by a rotated cone. -/
def normSquareDivEpigraph {n : Nat} :
    EpigraphRepr (fun p : EuclideanSpace ℝ (Fin n) × {y : ℝ // 0 < y} =>
      ‖p.1‖ ^ 2 / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, WithLp.ofLp p.1) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using norm_sq_div_le_iff p.1 p.2.1 t p.2.2

/-- A positive-denominator sum of squares represented by a rotated cone. -/
def sumSquaresDivEpigraph {n : Nat} :
    EpigraphRepr (fun p : (Fin n → ℝ) × {y : ℝ // 0 < y} =>
      (∑ i, p.1 i ^ 2) / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, fun i => p.1 i) ∈ (Cone.rotatedSecondOrder n).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using sumSquares_div_le_iff p.1 p.2.1 t p.2.2

/-- A positive-denominator scalar square represented by a rotated cone. -/
def squareDivEpigraph :
    EpigraphRepr (fun p : ℝ × {y : ℝ // 0 < y} => p.1 ^ 2 / p.2.1) where
  Auxiliary := Unit
  target p t _ := (t, p.2.1 / 2, ![p.1]) ∈ (Cone.rotatedSecondOrder 1).carrier
  source_iff_exists p t := by
    simpa only [exists_const] using square_div_le_iff p.1 p.2.1 t p.2.2

end Morew.Conic.SecondOrder
