/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Providing objective certificates

Use `conic using cert` or `qconic using cert` to supply a representation of
the objective. Constraints are converted automatically.
-/

@[expose] public section

namespace Examples.Advanced.ObjCertificate

open Morew
open scoped Matrix
noncomputable section

/-!
## An affine function

Given `f(x) = ax + b`, construct an affine certificate from this equality.
-/

def affineProblem (f : ℝ → ℝ) :=
  problem (x : ℝ)
    minimize f x
    subject to
      lower : 0 ≤ x
      upper : x ≤ 1

def affineCertificate (f : ℝ → ℝ) (a b : ℝ) (hf : ∀ x, f x = a * x + b) :
    Affine.Certified f where
  map := a • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ b
  correct x := (hf x).symm

section

variable (f : ℝ → ℝ) (a b : ℝ) (hf : ∀ x, f x = a * x + b)

reformulation affineConic : (affineProblem f) := by
  conic using affineCertificate f a b hf

#printp affineConic

example : GlobalEquiv (affineProblem f) (affineConic f) := affineConic.equiv f
example : (affineConic.conicForm f a b hf).data.toProblem = affineConic f :=
  (affineConic.conicForm f a b hf).represents

end

/-!
## A matrix quadratic

For a positive semidefinite matrix `P`, consider

```math
\begin{array}{ll}
\text{minimize} & x^T P x + c^T x + d \\
\text{subject to} & x \succeq 0.
\end{array}
```
-/

def matrixProblem {n : Nat} (P : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) (d : ℝ) :=
  problem (x : Fin n → ℝ)
    minimize x ⬝ᵥ (P *ᵥ x) + c ⬝ᵥ x + d
    subject to nonneg : x ∈ ℝ₊^n

/-!
The homogeneous quadratic part is `Q(x) = x^T P x`; the affine remainder is
`a(x) = c^T x + d`. Positive semidefiniteness gives `Q(x) ≥ 0` for every `x`.
These facts define the `QuadConic.CertifiedMin` certificate below.
-/

def matrixCertificate {n : Nat} (P : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) (d : ℝ) (hP : P.PosSemidef) :
    QuadConic.CertifiedMin (fun x => x ⬝ᵥ (P *ᵥ x) + c ⬝ᵥ x + d) where
  quadratic := P.toQuadraticForm'
  affine := (dotProductBilin ℝ ℝ c).toAffineMap + AffineMap.const ℝ _ d
  correct x := by
    simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', add_assoc]
  curvature x := by
    simpa [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using
      hP.dotProduct_mulVec_nonneg x

section

variable {n : Nat} (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (d : ℝ)
  (hP : P.PosSemidef)

reformulation matrixConic : (matrixProblem P c d) := by
  qconic using matrixCertificate P c d hP

#printp matrixConic

example : GlobalEquiv (matrixProblem P c d) (matrixConic P c d) :=
  matrixConic.equiv P c d
example : (matrixConic.quadConicForm P c d hP).data.toProblem = matrixConic P c d :=
  (matrixConic.quadConicForm P c d hP).represents

/-!
For maximization, `QuadConic.CertifiedMax f` requires the homogeneous quadratic
part to satisfy `Q(x) ≤ 0` for every `x`.

In fact, the hypothesis `P.PosSemidef` lets `qconic` construct the objective certificate
automatically.
-/

reformulation matrixConicAutomatic : (matrixProblem P c d) := by
  qconic

example : GlobalEquiv (matrixProblem P c d) (matrixConicAutomatic P c d) :=
  matrixConicAutomatic.equiv P c d
example : IsQuadConic (matrixConicAutomatic P c d) :=
  matrixConicAutomatic.isQuadConic P c d hP
example : (matrixConicAutomatic.quadConicForm P c d hP).data.toProblem =
    matrixConicAutomatic P c d :=
  (matrixConicAutomatic.quadConicForm P c d hP).represents

/-!
To obtain an affine objective, introduce a bound `xᵀPx ≤ t` and minimize
`t + cᵀx + d`. The positive semidefinite square root `R` of `P` satisfies

```math
P=R^T R,\qquad x^T P x=\lVert Rx\rVert_2^2.
```

The bound is therefore equivalent to `(t, 1/2, Rx) ∈ RSOCₙ`.
-/

reformulation matrixEpigraphConic : (matrixProblem P c d) := by
  epigraph t at (x ⬝ᵥ (P *ᵥ x)) as quadraticBound
  conic

#printp matrixEpigraphConic

example : GlobalEquiv (matrixProblem P c d) (matrixEpigraphConic P c d) :=
  matrixEpigraphConic.equiv P c d hP
example : IsConic (matrixEpigraphConic P c d) :=
  matrixEpigraphConic.isConic P c d
example : (matrixEpigraphConic.conicForm P c d).data.toProblem =
    matrixEpigraphConic P c d :=
  (matrixEpigraphConic.conicForm P c d).represents

end
end
end Examples.Advanced.ObjCertificate
