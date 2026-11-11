/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Supplied objective certificates preserve exact objectives, directions, and recovery. -/

namespace MorewTest.Reformulation.ObjectiveCertificates

open Morew Matrix
noncomputable section

def minimum (f : ℝ → ℝ) := problem (x : ℝ) minimize f x

def maximum (f : ℝ → ℝ) := problem (x : ℝ) maximize f x

opaque affineCertificate (f : ℝ → ℝ) (cert : Affine.Certified f) :
    Affine.Certified f := cert

opaque minCertificate (f : ℝ → ℝ) (cert : QuadConic.CertifiedMin f) :
    QuadConic.CertifiedMin f := cert

opaque maxCertificate (f : ℝ → ℝ) (cert : QuadConic.CertifiedMax f) :
    QuadConic.CertifiedMax f := cert

section Local

variable (f : ℝ → ℝ) (affine : Affine.Certified f)
  (convex : QuadConic.CertifiedMin f) (concave : QuadConic.CertifiedMax f)

reformulation affineMin : (minimum f) := by
  conic using affine

reformulation affineMax : (maximum f) := by
  conic using affineCertificate f affine

reformulation affineRecord : (minimum f) := by
  conic using { map := affine.map, correct := affine.correct }

reformulation quadraticMin : (minimum f) := by
  qconic using minCertificate f convex

reformulation quadraticMax : (maximum f) := by
  qconic using (by exact concave)

reformulation zeroMin : (minimum f) := by
  qconic using {
    quadratic := 0
    affine := affine.map
    correct := fun x => by simpa using affine.correct x
    curvature := fun _ => le_rfl }

reformulation zeroMax : (maximum f) := by
  qconic using QuadConic.CertifiedMax.ofAffine affine

example : GlobalEquiv (minimum f) (affineMin f) := affineMin.equiv f
example : Conic.Form (affineMin f) := affineMin.conicForm f affine
example : (affineMax.conicForm f affine).data.sense = .maximize := rfl
example : IsConic (affineRecord f) := affineRecord.isConic f affine
example : QuadConic.Form (quadraticMin f) := quadraticMin.quadConicForm f convex
example : QuadConic.Form (quadraticMax f) := quadraticMax.quadConicForm f concave
example : (quadraticMin.quadConicForm f convex).data.sense = .minimize := rfl
example : (quadraticMax.quadConicForm f concave).data.sense = .maximize := rfl
example (x : ℝ) : (quadraticMin f).objective x = f x := rfl
example : (zeroMin.quadConicForm f affine).data.quadratic = 0 := rfl
example : (zeroMax.quadConicForm f affine).data.quadratic = 0 := rfl

end Local

section Matrices

variable {n : Nat}

def matrixObjective (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ)
    (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x) + c ⬝ᵥ x + d

def remainder (c : Fin n → ℝ) (d : ℝ) :
    Affine.Certified (fun x => c ⬝ᵥ x + d) :=
  (Affine.Certified.dotConstLeft c (Affine.Certified.id _)).add (Affine.Certified.const _ d)

def matrixExpr (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ) :
    QuadConic.CertifiedExpr (matrixObjective P c d) where
  quadratic := P.toQuadraticForm'
  affine := (remainder c d).map
  correct x := by
    rw [(remainder c d).correct]
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', matrixObjective]
    ring

def matrixMin (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hP : P.PosSemidef) : QuadConic.CertifiedMin (matrixObjective P c d) where
  toCertifiedExpr := matrixExpr P c d
  curvature x := by
    simpa [matrixExpr, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using
      hP.dotProduct_mulVec_nonneg x

def matrixMax (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ)
    (hP : P.PosSemidef) : QuadConic.CertifiedMax (fun x => -matrixObjective P c d x) where
  toCertifiedExpr := (matrixExpr P c d).neg
  curvature x := neg_nonpos.mpr ((matrixMin P c d hP).curvature x)

def matrixProblem (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ) :=
  problem (x : Fin n → ℝ)
    minimize matrixObjective P c d x
    subject to nonneg : 0 ≤ x

def matrixMaximum (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ) :=
  problem (x : Fin n → ℝ) maximize -matrixObjective P c d x

variable (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ) (hP : P.PosSemidef)

reformulation matrixTarget : (matrixProblem P c d) := by
  qconic using matrixMin P c d hP

reformulation matrixMaxTarget : (matrixMaximum P c d) := by
  qconic using matrixMax P c d hP

example : QuadConic.Form (matrixTarget P c d) := matrixTarget.quadConicForm P c d hP
example : GlobalEquiv (matrixProblem P c d) (matrixTarget P c d) := matrixTarget.equiv P c d
example (x : Fin n → ℝ) : (matrixTarget P c d).objective x =
    x ⬝ᵥ (P *ᵥ x) + c ⬝ᵥ x + d := rfl
example (x : Fin n → ℝ) : (matrixTarget P c d).feasible x ↔ 0 ≤ x := Iff.rfl
example : (matrixMaxTarget.quadConicForm P c d hP).data.sense = .maximize := rfl
example : (matrixTarget.quadConicForm P c d hP).data.toProblem.objective 0 = d := by
  rw [(matrixTarget.quadConicForm P c d hP).represents]
  simp [matrixTarget, matrixObjective]

example : IsQuadConic (matrixTarget (0 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2] 7) :=
  matrixTarget.isQuadConic _ _ _ Matrix.PosSemidef.zero

private def singularMatrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]

private theorem singularPSD : singularMatrix.PosSemidef :=
  Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)

example : IsQuadConic (matrixTarget singularMatrix ![2, 3] 11) :=
  matrixTarget.isQuadConic _ _ _ singularPSD

example : (matrixMin singularMatrix ![2, 3] 11 singularPSD).quadratic ![0, 1] = 0 := by
  norm_num [matrixMin, matrixExpr, singularMatrix, Matrix.toQuadraticForm',
    Matrix.toLinearMap₂'_apply', Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Matrices

section Auxiliaries

variable (f : ℝ × ℝ → ℝ) (affine : Affine.Certified f)
  (convex : QuadConic.CertifiedMin f)

def twoAuxiliaries (f : ℝ × ℝ → ℝ) :=
  problem (x t : ℝ)
    minimize f (x, t)
    subject to
      first : Fn.softplus x ≤ t
      second : Fn.softplus (-x) ≤ t

reformulation affineAuxiliaries : (twoAuxiliaries f) := by
  conic using affine

reformulation quadraticAuxiliaries : (twoAuxiliaries f) := by
  qconic using convex

example : (affineAuxiliaries.conicForm f affine).data.rowCount = 4 := rfl
example : (quadraticAuxiliaries.quadConicForm f convex).data.rowCount = 4 := rfl
example (x t : ℝ) (u v : Fin 2 → ℝ) :
    (affineAuxiliaries f).objective (((x, t), u), v) = f (x, t) := rfl
example (x t : ℝ) (u v : Fin 2 → ℝ) :
    (quadraticAuxiliaries f).objective (((x, t), u), v) = f (x, t) := rfl
example (z : FeasiblePoint (affineAuxiliaries f)) :
    ((affineAuxiliaries.equiv f).backward.map z).val = z.val.1.1 := rfl
example (z : FeasiblePoint (quadraticAuxiliaries f)) :
    ((quadraticAuxiliaries.equiv f).backward.map z).val = z.val.1.1 := rfl
example (z : ((ℝ × ℝ) × (Fin 2 → ℝ)) × (Fin 2 → ℝ)) :
    (quadraticAuxiliaries.quadConicForm f convex).data.toProblem.feasible z ↔
      (quadraticAuxiliaries f).feasible z := by
  rw [(quadraticAuxiliaries.quadConicForm f convex).represents]

end Auxiliaries

def nonlinear := problem (x : ℝ) minimize (x - 3) ^ 2

reformulation currentObjective : nonlinear := by
  epigraph t
  conic using (Affine.Certified.id (ℝ × ℝ)).snd

example : GlobalEquiv nonlinear currentObjective := currentObjective.equiv
example : IsConic currentObjective := currentObjective.isConic
example (x t : ℝ) : currentObjective.objective (x, t) = t := rfl

def zeroIndefinite := problem (x y : ℝ) minimize 0 * (x ^ 2 - y ^ 2) + 7

def zeroIndefiniteMax := problem (x y : ℝ) maximize 0 * (x ^ 2 - y ^ 2) + 7

reformulation zeroIndefiniteTarget : zeroIndefinite := by qconic
reformulation zeroIndefiniteMaxTarget : zeroIndefiniteMax := by qconic

example : IsQuadConic zeroIndefiniteTarget := zeroIndefiniteTarget.isQuadConic
example : IsQuadConic zeroIndefiniteMaxTarget := zeroIndefiniteMaxTarget.isQuadConic
example (x y : ℝ) : zeroIndefiniteTarget.objective (x, y) = 7 := by
  change 0 * (x ^ 2 - y ^ 2) + 7 = 7
  ring

end
end MorewTest.Reformulation.ObjectiveCertificates
