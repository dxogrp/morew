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

private def shiftedSquare : Certified (fun x : ℝ => (x + 3) ^ 2) :=
  Certified.square shifted

example (x : ℝ) : shiftedSquare.quadratic x + shiftedSquare.affine x = (x + 3) ^ 2 :=
  shiftedSquare.correct x

example : shiftedSquare.affine 0 = 9 := by
  norm_num [shiftedSquare, shifted, Certified.square, Affine.Certified.add,
    Affine.Certified.id, Affine.Certified.const, AffineMap.const]

private def minimumData : Data ℝ where
  sense := .minimize
  quadratic := shiftedSquare.quadratic
  affine := shiftedSquare.affine
  curvature := Certified.square_nonnegative shifted
  rowCount := 0
  constraints := Fin.elim0

private def maximumData : Data ℝ where
  sense := .maximize
  quadratic := shiftedSquare.neg.quadratic
  affine := shiftedSquare.neg.affine
  curvature := Certified.neg_nonpositive shiftedSquare (Certified.square_nonnegative shifted)
  rowCount := 0
  constraints := Fin.elim0

example (x : ℝ) : minimumData.toProblem.objective x = (x + 3) ^ 2 :=
  shiftedSquare.correct x

example (x : ℝ) : maximumData.toProblem.objective x = -(x + 3) ^ 2 :=
  shiftedSquare.neg.correct x

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

example : (Certified.square firstCoordinate).Nonnegative :=
  Certified.square_nonnegative firstCoordinate

example : (Certified.square firstCoordinate).quadratic (0, 1) = 0 := by
  norm_num [Certified.square, firstCoordinate, Affine.Certified.fst, Affine.Certified.id]

example (c : ℝ) :
    (Certified.smul c (Certified.ofAffine shifted)).quadratic = 0 := by
  simp [Certified.smul]

-- Rectangular matrices and their affine offsets are retained exactly.
private def residual {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Affine.Certified (fun x : Fin n → ℝ => A *ᵥ x - b) :=
  ((Affine.Certified.id (Fin n → ℝ)).mulVec A).sub (Affine.Certified.const _ b)

example {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    (Certified.fnNorm2Sq (residual A b)).quadratic x +
      (Certified.fnNorm2Sq (residual A b)).affine x = Fn.norm2 (A *ᵥ x - b) ^ 2 :=
  (Certified.fnNorm2Sq (residual A b)).correct x

example {n : Nat} (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ)
    (x : Fin n → ℝ) :
    (Certified.fnNorm2Sq (residual A b)).quadratic x +
      (Certified.fnNorm2Sq (residual A b)).affine x = 0 := by
  rw [(Certified.fnNorm2Sq (residual A b)).correct]
  simp

example {n : Nat} (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) :
    (Certified.fnNorm2Sq (residual A b)).Nonpositive :=
  Certified.fnNorm2Sq_empty_nonpositive (residual A b)

example {m : Nat} (A : Matrix (Fin m) (Fin 0) ℝ) (b : Fin m → ℝ)
    (x : Fin 0 → ℝ) :
    (Certified.fnNorm2Sq (residual A b)).quadratic x +
      (Certified.fnNorm2Sq (residual A b)).affine x = Fn.norm2 (A *ᵥ x - b) ^ 2 :=
  (Certified.fnNorm2Sq (residual A b)).correct x

example (x : ℝ) :
    (Certified.sum (∅ : Finset Nat) (fun _ => shiftedSquare)).quadratic x +
      (Certified.sum (∅ : Finset Nat) (fun _ => shiftedSquare)).affine x = 0 := by
  simpa using (Certified.sum (∅ : Finset Nat) (fun _ => shiftedSquare)).correct x

example (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    (shiftedSquare.divConst c hc).quadratic x +
      (shiftedSquare.divConst c hc).affine x = (x + 3) ^ 2 / c :=
  (shiftedSquare.divConst c hc).correct x

end

end MorewTest.QuadConic.Basic
