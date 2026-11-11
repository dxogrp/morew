/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.QuadConic

/-! Exact quadratic representations and curvature, independently of elaboration. -/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.QuadConic.Basic

open Morew Morew.QuadConic
open scoped Matrix

noncomputable section

private def shifted : Affine.Certified (fun x : ℝ => x + 3) :=
  (Affine.Certified.id ℝ).add (Affine.Certified.const ℝ 3)

private def shiftedSquare : CertifiedExpr (fun x : ℝ => (x + 3) ^ 2) :=
  CertifiedExpr.square shifted

example (x : ℝ) : shiftedSquare.quadratic x + shiftedSquare.affine x = (x + 3) ^ 2 :=
  shiftedSquare.correct x

example : shiftedSquare.affine 0 = 9 := by
  norm_num [shiftedSquare, shifted, CertifiedExpr.square, Affine.Certified.add,
    Affine.Certified.id, Affine.Certified.const, AffineMap.const]

private def minimumCertificate : CertifiedMin (fun x : ℝ => (x + 3) ^ 2) where
  toCertifiedExpr := shiftedSquare
  curvature := CertifiedExpr.square_nonneg shifted

private def maximumCertificate : CertifiedMax (fun x : ℝ => -(x + 3) ^ 2) where
  toCertifiedExpr := shiftedSquare.neg
  curvature := CertifiedExpr.neg_nonpos shiftedSquare (CertifiedExpr.square_nonneg shifted)

private def minimumData : Data ℝ where
  sense := .minimize
  quadratic := minimumCertificate.quadratic
  affine := minimumCertificate.affine
  curvature := minimumCertificate.curvature
  rowCount := 0
  constraints := Fin.elim0

private def maximumData : Data ℝ where
  sense := .maximize
  quadratic := maximumCertificate.quadratic
  affine := maximumCertificate.affine
  curvature := maximumCertificate.curvature
  rowCount := 0
  constraints := Fin.elim0

example (x : ℝ) : minimumData.toProblem.objective x = (x + 3) ^ 2 :=
  shiftedSquare.correct x

example (x : ℝ) : maximumData.toProblem.objective x = -(x + 3) ^ 2 :=
  shiftedSquare.neg.correct x

-- Auxiliary coordinates do not change the objective or its curvature.
private def liftedMinimum : CertifiedMin (fun x : ℝ × ℝ => (x.1 + 3) ^ 2) :=
  minimumCertificate.comp (LinearMap.fst ℝ ℝ ℝ)

private def liftedMaximum : CertifiedMax (fun x : ℝ × ℝ => -(x.1 + 3) ^ 2) :=
  maximumCertificate.comp (LinearMap.fst ℝ ℝ ℝ)

example (x : ℝ × ℝ) :
    liftedMinimum.quadratic x + liftedMinimum.affine x = (x.1 + 3) ^ 2 :=
  liftedMinimum.correct x

example (x : ℝ × ℝ) :
    liftedMaximum.quadratic x + liftedMaximum.affine x = -(x.1 + 3) ^ 2 :=
  liftedMaximum.correct x

example (x : ℝ × ℝ) : 0 ≤ liftedMinimum.quadratic x := liftedMinimum.curvature x

example (x : ℝ × ℝ) : liftedMaximum.quadratic x ≤ 0 := liftedMaximum.curvature x

example : liftedMinimum.quadratic (0, 1) = 0 := by
  norm_num [liftedMinimum, minimumCertificate, shiftedSquare, shifted,
    CertifiedMin.comp, CertifiedExpr.comp, CertifiedExpr.square, Affine.Certified.add,
    Affine.Certified.id, Affine.Certified.const]

example : liftedMinimum.affine (0, 1) = 9 := by
  norm_num [liftedMinimum, minimumCertificate, shiftedSquare, shifted,
    CertifiedMin.comp, CertifiedExpr.comp, CertifiedExpr.square, Affine.Certified.add,
    Affine.Certified.id, Affine.Certified.const, AffineMap.const]

-- A nonconstant affine objective has zero quadratic part in either direction.
example : (CertifiedMin.ofAffine shifted).quadratic = 0 := rfl

example : (CertifiedMax.ofAffine shifted).quadratic = 0 := rfl

example (x : ℝ) : (CertifiedMin.ofAffine shifted).affine x = x + 3 := shifted.correct x

example (x : ℝ) : (CertifiedMax.ofAffine shifted).affine x = x + 3 := shifted.correct x

-- Affine precomposition retains offsets in the coordinate map and the function.
example (x : ℝ) : (shifted.comp shifted.map).map x = x + 6 := by
  rw [(shifted.comp shifted.map).correct, shifted.correct]
  ring

example : ConvexOn ℝ Set.univ minimumData.toProblem.objective :=
  minimumData.objective_convexOn rfl

example : ConcaveOn ℝ Set.univ maximumData.toProblem.objective :=
  maximumData.objective_concaveOn rfl

example (x : ℝ) : minimumData.toProblem.feasible x := by
  intro i
  exact Fin.elim0 i

example : IsQuadConic minimumData.toProblem := (Form.mk minimumData rfl).isQuadConic

example : IsQuadConic maximumData.toProblem := (Form.mk maximumData rfl).isQuadConic

-- Abstract decision spaces require no ambient norm or coordinates.
example {X : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    (data : Conic.Data X) : (Data.ofConic data).toProblem = data.toProblem :=
  Data.ofConic_toProblem data

example {X : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    (data : Conic.Data X) : (Data.ofConic data).constraints = data.constraints := rfl

example {X : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    {p : Problem X ℝ} (form : Conic.Form p) : IsQuadConic p :=
  (Form.ofConic form).isQuadConic

example {X : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
    {p : Problem X ℝ} (form : Conic.Form p) :
    (Form.ofConic form).data.sense = form.data.sense := rfl

-- One squared coordinate gives singular curvature on a product space.
private def firstCoordinate : Affine.Certified (fun x : ℝ × ℝ => x.1) :=
  (Affine.Certified.id (ℝ × ℝ)).fst

example : (CertifiedExpr.square firstCoordinate).Nonneg :=
  CertifiedExpr.square_nonneg firstCoordinate

example : (CertifiedExpr.square firstCoordinate).quadratic (0, 1) = 0 := by
  norm_num [CertifiedExpr.square, firstCoordinate, Affine.Certified.fst, Affine.Certified.id]

example (c : ℝ) :
    (CertifiedExpr.smul c (CertifiedExpr.ofAffine shifted)).quadratic = 0 := by
  simp [CertifiedExpr.smul]

-- Rectangular matrices and their affine offsets are retained exactly.
private def residual {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Affine.Certified (fun x : Fin n → ℝ => A *ᵥ x - b) :=
  ((Affine.Certified.id (Fin n → ℝ)).mulVec A).sub (Affine.Certified.const _ b)

example {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    (CertifiedExpr.fnNorm2Sq (residual A b)).quadratic x +
      (CertifiedExpr.fnNorm2Sq (residual A b)).affine x = Fn.norm2 (A *ᵥ x - b) ^ 2 :=
  (CertifiedExpr.fnNorm2Sq (residual A b)).correct x

example {n : Nat} (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ)
    (x : Fin n → ℝ) :
    (CertifiedExpr.fnNorm2Sq (residual A b)).quadratic x +
      (CertifiedExpr.fnNorm2Sq (residual A b)).affine x = 0 := by
  rw [(CertifiedExpr.fnNorm2Sq (residual A b)).correct]
  simp

example {n : Nat} (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) :
    (CertifiedExpr.fnNorm2Sq (residual A b)).Nonpos :=
  CertifiedExpr.fnNorm2Sq_empty_nonpos (residual A b)

example {m : Nat} (A : Matrix (Fin m) (Fin 0) ℝ) (b : Fin m → ℝ)
    (x : Fin 0 → ℝ) :
    (CertifiedExpr.fnNorm2Sq (residual A b)).quadratic x +
      (CertifiedExpr.fnNorm2Sq (residual A b)).affine x = Fn.norm2 (A *ᵥ x - b) ^ 2 :=
  (CertifiedExpr.fnNorm2Sq (residual A b)).correct x

example (x : ℝ) :
    (CertifiedExpr.sum (∅ : Finset Nat) (fun _ => shiftedSquare)).quadratic x +
      (CertifiedExpr.sum (∅ : Finset Nat) (fun _ => shiftedSquare)).affine x = 0 := by
  simpa using (CertifiedExpr.sum (∅ : Finset Nat) (fun _ => shiftedSquare)).correct x

example (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    (shiftedSquare.divConst c hc).quadratic x +
      (shiftedSquare.divConst c hc).affine x = (x + 3) ^ 2 / c :=
  (shiftedSquare.divConst c hc).correct x

end

end MorewTest.QuadConic.Basic
