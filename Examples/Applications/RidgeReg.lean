/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.QuadConic
import Morew.Reformulation.NLP

/-!
# Ridge regression

Given matrices `A ∈ ℝᵐˣⁿ`, `C ∈ ℝᵏˣⁿ`, vectors `b ∈ ℝᵐ`, `d ∈ ℝᵏ`,
and a weight `λ ≥ 0`, choose `x ∈ ℝⁿ` to solve

```math
\begin{array}{ll}
\text{minimize} & \lVert Ax-b\rVert_2^2 + \lambda\lVert x\rVert_2^2 \\
\text{subject to} & Cx=d.
\end{array}
```

The first term fits the observations `b`; the second controls the size of `x`.
The equations impose linear constraints. We obtain four equivalent formulations.
-/

namespace Examples.Applications.RidgeReg

open Morew
open scoped Matrix
noncomputable section

def leastSquares (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) (d : Fin k → ℝ) (weight : ℝ) :=
  problem (x : Fin n → ℝ)
    let loss := Fn.norm2 (A *ᵥ x - b) ^ 2
    let penalty := Fn.norm2 x ^ 2
    minimize loss + weight * penalty
    subject to
      balance : C *ᵥ x = d

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
  (C : Matrix (Fin k) (Fin n) ℝ) (d : Fin k → ℝ) (weight : ℝ)

/-!
## Smooth formulation

The quadratic objective and linear equations are smooth. This path keeps
the original variable and objective.
-/

reformulation smooth : (leastSquares A b C d weight) := by
  nlp

#printp smooth

example : GlobalEquiv (leastSquares A b C d weight) (smooth A b C d weight) :=
  smooth.equiv A b C d weight
example : IsSmoothNLP (smooth A b C d weight) := smooth.isSmoothNLP A b C d weight
example : (smooth.nlpForm A b C d weight).data.toProblem = smooth A b C d weight :=
  (smooth.nlpForm A b C d weight).represents

/-!
## Quadratic conic formulation

The `qconic` command keeps the quadratic objective and represents `Cx=d` by a
zero-cone constraint. The decomposition is

```math
Q(x)=\lVert Ax\rVert_2^2+\lambda\lVert x\rVert_2^2,
\qquad a(x)=-2\langle Ax,b\rangle+\lVert b\rVert_2^2.
```

The assumption `λ ≥ 0` proves that `Q` is nonnegative, including at `λ = 0`.
No Gram matrix is formed. In the coordinate convention
`(1/2)xᵀPx + qᵀx + r`, these data correspond to
`P = 2(AᵀA + λI)`, `q = -2Aᵀb`, and `r = bᵀb`.
-/

variable (hweight : 0 ≤ weight)

include hweight in
reformulation direct : (leastSquares A b C d weight) := by
  qconic

#printp direct

example : GlobalEquiv (leastSquares A b C d weight) (direct A b C d weight) :=
  direct.equiv A b C d weight
example : IsQuadConic (direct A b C d weight) :=
  direct.isQuadConic A b C d weight hweight
example : (direct.quadConicForm A b C d weight hweight).data.toProblem =
    direct A b C d weight := (direct.quadConicForm A b C d weight hweight).represents
example (x : Fin n → ℝ) : (direct A b C d weight).objective x =
    Fn.norm2 (A *ᵥ x - b) ^ 2 + weight * Fn.norm2 x ^ 2 := rfl
example (x : Fin n → ℝ) : (direct A b C d weight).feasible x ↔ C *ᵥ x = d := by
  change C *ᵥ x - d = 0 ↔ C *ᵥ x = d
  exact sub_eq_zero

/-- The constant term and affine cross term are retained exactly. -/
theorem objectiveDecomposition (x : Fin n → ℝ) :
    (leastSquares A b C d weight).objective x =
      (Fn.norm2 (A *ᵥ x) ^ 2 + weight * Fn.norm2 x ^ 2) +
        (-2 * (A *ᵥ x) ⬝ᵥ b + Fn.norm2 b ^ 2) := by
  change Fn.norm2 (A *ᵥ x - b) ^ 2 + weight * Fn.norm2 x ^ 2 = _
  simp only [Fn.norm2_sq_eq_sum, Pi.sub_apply, dotProduct]
  have expansion : (∑ i, ((A *ᵥ x) i - b i) ^ 2) =
      (∑ i, (A *ᵥ x) i ^ 2) - 2 * (∑ i, (A *ᵥ x) i * b i) + ∑ i, b i ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [expansion]
  ring

/-- The generated form stores the homogeneous part of the ridge objective. -/
theorem directQuadratic (x : Fin n → ℝ) :
    (direct.quadConicForm A b C d weight hweight).data.quadratic x =
      Fn.norm2 (A *ᵥ x) ^ 2 + weight * Fn.norm2 x ^ 2 := by
  change inner (𝕜 := ℝ) (WithLp.toLp 2 (A *ᵥ x - 0)) (WithLp.toLp 2 (A *ᵥ x - 0)) +
    weight * inner (𝕜 := ℝ) (WithLp.toLp 2 x) (WithLp.toLp 2 x) = _
  simp only [sub_zero, real_inner_self_eq_norm_sq, Fn.norm2]

/-- The generated affine part stores the cross term and the constant term. -/
theorem directAffine (x : Fin n → ℝ) :
    (direct.quadConicForm A b C d weight hweight).data.affine x =
      -2 * (A *ᵥ x) ⬝ᵥ b + Fn.norm2 b ^ 2 := by
  have represented := congrArg (fun p : Problem (Fin n → ℝ) ℝ => p.objective x)
    (direct.quadConicForm A b C d weight hweight).represents
  change (direct.quadConicForm A b C d weight hweight).data.quadratic x +
    (direct.quadConicForm A b C d weight hweight).data.affine x =
      (leastSquares A b C d weight).objective x at represented
  rw [directQuadratic] at represented
  linarith [objectiveDecomposition A b C d weight x]

include hweight in
/-- Nonnegative ridge weights give nonnegative homogeneous quadratic curvature. -/
theorem quadraticNonnegative (x : Fin n → ℝ) :
    0 ≤ Fn.norm2 (A *ᵥ x) ^ 2 + weight * Fn.norm2 x ^ 2 :=
  add_nonneg (sq_nonneg _) (mul_nonneg hweight (sq_nonneg _))

example : IsQuadConic (direct A b C d 0) :=
  direct.isQuadConic A b C d 0 (le_refl 0)

example {z : FeasiblePoint (direct A b C d weight)}
    (hz : (direct A b C d weight).IsGlobalOptimum z) :
    (leastSquares A b C d weight).IsGlobalOptimum
      ((direct.equiv A b C d weight).backward.map z) :=
  (direct.equiv A b C d weight).map_isGlobalOptimum_backward hz

/-!
## Two cone constraints

Introduce bounds `‖Ax-b‖₂² ≤ t` and `‖x‖₂² ≤ s`, and minimize `t + λs`.
Each bound becomes a rotated second-order cone constraint. The assumption
`λ ≥ 0` ensures that increasing the penalty bound cannot decrease the objective.
-/

reformulation separate : (leastSquares A b C d weight) := by
  epigraph t at loss as lossBound
  epigraph s at penalty as penaltyBound
  conic

#printp separate

example : GlobalEquiv (leastSquares A b C d weight) (separate A b C d weight) :=
  separate.equiv A b C d weight hweight
example : IsConic (separate A b C d weight) := separate.isConic A b C d weight
example : (separate.conicForm A b C d weight).data.toProblem = separate A b C d weight :=
  (separate.conicForm A b C d weight).represents

/-!
## One cone constraint

Join the two vectors using

```math
\widetilde A=\begin{bmatrix}A\\\sqrt{\lambda}I\end{bmatrix},
\qquad \widetilde b=\begin{bmatrix}b\\0\end{bmatrix}.
```

Then `‖Ãx-b̃‖₂² = ‖Ax-b‖₂² + λ‖x‖₂²`. The following rule represents an
upper bound on this sum by one rotated second-order cone constraint.
-/

def combinedMatrix (A : Matrix (Fin m) (Fin n) ℝ) (weight : ℝ) :
    Matrix (Fin (m + n)) (Fin n) ℝ :=
  Fin.append (fun i j => A i j)
    (fun i j => Real.sqrt weight * (1 : Matrix (Fin n) (Fin n) ℝ) i j)

def combinedData (b : Fin m → ℝ) : Fin (m + n) → ℝ := Fin.append b 0

theorem combinedResidual (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (weight : ℝ) (x : Fin n → ℝ) :
    combinedMatrix A weight *ᵥ x - combinedData (n := n) b =
      Fin.append (A *ᵥ x - b) (fun j => Real.sqrt weight * x j) := by
  ext i
  induction i using Fin.addCases <;>
    simp [combinedMatrix, combinedData, Matrix.mulVec, dotProduct, Matrix.one_apply]

def combinedEpigraph (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (weight : ℝ) (hweight : 0 ≤ weight) :
    EpigraphRepr (fun x : Fin n → ℝ =>
      Fn.norm2 (A *ᵥ x - b) ^ 2 + weight * Fn.norm2 x ^ 2) where
  Auxiliary := Unit
  target x q _ := (q, 1 / 2, combinedMatrix A weight *ᵥ x - combinedData (n := n) b) ∈
    (Conic.Cone.rotatedSecondOrder (m + n)).carrier
  source_iff_exists x q := by
    simp only [exists_const, combinedResidual]
    simpa [Fn.norm2_sq_eq_sum, Fin.sum_univ_add, mul_pow,
      Real.sq_sqrt hweight, Finset.mul_sum] using
      Conic.SecondOrder.sumSquares_le_iff
        (Fin.append (A *ᵥ x - b) (fun j => Real.sqrt weight * x j)) q

reformulation combined : (leastSquares A b C d weight) := by
  epigraph q as objectiveBound
  conic at objectiveBound using (combinedEpigraph A b weight hweight)
  conic

#printp combined

example : GlobalEquiv (leastSquares A b C d weight) (combined A b C d weight) :=
  combined.equiv A b C d weight hweight
example : IsConic (combined A b C d weight) := combined.isConic A b C d weight
example : (combined.conicForm A b C d weight).data.toProblem = combined A b C d weight :=
  (combined.conicForm A b C d weight).represents

/-!
All four formulations retain `x` and the equations `Cx=d`. The affine conic
forms add bound variables. Their equivalence certificates recover `x` and transfer
global optimality to the original problem.
The conic alternatives remain useful when a later matrix-based representation
of the quadratic objective would lose sparsity by forming `AᵀA`.
-/

example {z : FeasiblePoint (combined A b C d weight)}
    (hz : (combined A b C d weight).IsGlobalOptimum z) :
    (leastSquares A b C d weight).IsGlobalOptimum
      ((combined.equiv A b C d weight hweight).backward.map z) :=
  (combined.equiv A b C d weight hweight).map_isGlobalOptimum_backward hz

end
end Examples.Applications.RidgeReg
