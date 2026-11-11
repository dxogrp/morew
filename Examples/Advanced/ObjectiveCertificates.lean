/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Providing objective certificates

Use `conic using cert` or `qconic using cert` when the objective has a known
representation that automatic recognition cannot establish. The certificate
describes the current objective; the command still converts the constraints.
-/

namespace Examples.Advanced.ObjectiveCertificates

open Morew
open scoped Matrix
noncomputable section

/-!
## An affine function

Suppose `f(x) = ax + b`. The hypothesis gives an exact affine representation
even when the definition of `f` is unavailable.
-/

def affineCertificate (f : ℝ → ℝ) (a b : ℝ) (hf : ∀ x, f x = a * x + b) :
    Affine.Certified f where
  map := a • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ b
  correct x := (hf x).symm

def affineProblem (f : ℝ → ℝ) :=
  problem (x : ℝ)
    minimize f x
    subject to
      lower : 0 ≤ x
      upper : x ≤ 1

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
\text{subject to} & x \geq 0.
\end{array}
```

The homogeneous quadratic part is `Q(x) = x^T P x`; the affine remainder is
`a(x) = c^T x + d`. Positive semidefiniteness gives `Q(x) ≥ 0` for every `x`,
including when `P` is singular or zero.
-/

def matrixProblem {n : Nat} (P : Matrix (Fin n) (Fin n) ℝ)
    (c : Fin n → ℝ) (d : ℝ) :=
  problem (x : Fin n → ℝ)
    minimize x ⬝ᵥ (P *ᵥ x) + c ⬝ᵥ x + d
    subject to nonneg : x ∈ ℝ₊^n

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

end

/-!
For maximization, supply `QuadConic.CertifiedMax f` with a proof that its
quadratic part is nonpositive. `CertifiedMin.ofAffine` and
`CertifiedMax.ofAffine` certify affine objectives with zero quadratic part in
the respective directions.
-/

end
end Examples.Advanced.ObjectiveCertificates
