/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Least squares

Given matrices `A ∈ ℝᵐˣⁿ`, `C ∈ ℝᵏˣⁿ`, vectors `b ∈ ℝᵐ`, `d ∈ ℝᵏ`,
and a weight `λ ≥ 0`, choose `x ∈ ℝⁿ` to solve

```math
\begin{array}{ll}
\text{minimize} & \lVert Ax-b\rVert_2^2 + \lambda\lVert x\rVert_2^2 \\
\text{subject to} & Cx=d.
\end{array}
```

The first term fits the observations `b`; the second controls the size of `x`.
The equations impose linear constraints. We write the squared norms as sums
of squares and obtain three equivalent formulations.
-/

namespace Examples.Applications.RidgeReg

open Morew
open scoped Matrix
noncomputable section

def leastSquares (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) (d : Fin k → ℝ) (weight : ℝ) :=
  problem (x : Fin n → ℝ)
    let loss := ∑ i, ((∑ j, A i j * x j) - b i) ^ 2
    let penalty := ∑ j, x j ^ 2
    minimize loss + weight * penalty
    subject to
      balance : (fun i => ∑ j, C i j * x j) = d

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

/-!
## Two cone constraints

Introduce bounds `‖Ax-b‖₂² ≤ t` and `‖x‖₂² ≤ s`, and minimize `t + λs`.
Each bound becomes a rotated second-order cone constraint. The assumption
`λ ≥ 0` ensures that increasing the penalty bound cannot decrease the objective.
-/

variable (hweight : 0 ≤ weight)

reformulation separate : (leastSquares A b C d weight) := by
  epigraph t at loss as lossBound
  epigraph s at penalty as penaltyBound using (by
    constructor
    · intro p; rfl
    · intro p _ s hs
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hweight))
  conic

#printp separate

example : GlobalEquiv (leastSquares A b C d weight) (separate A b C d weight) :=
  separate.equiv A b C d weight hweight
example : IsConic (separate A b C d weight) := separate.isConic A b C d weight

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
      (∑ i, ((∑ j, A i j * x j) - b i) ^ 2) + weight * ∑ j, x j ^ 2) where
  Auxiliary := Unit
  target x q _ := (q, 1 / 2, combinedMatrix A weight *ᵥ x - combinedData (n := n) b) ∈
    (Conic.Cone.rotatedSecondOrder (m + n)).carrier
  source_iff_exists x q := by
    simp only [exists_const, combinedResidual]
    simpa [Fin.sum_univ_add, mul_pow, Real.sq_sqrt hweight, Finset.mul_sum,
      Matrix.mulVec, dotProduct] using
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

/-!
All three formulations retain `x` and the equations `Cx=d`. The conic forms
add bound variables. Their equivalence certificates recover `x` and transfer
global optimality to the original problem.
-/

example {z : FeasiblePoint (combined A b C d weight)}
    (hz : (combined A b C d weight).IsGlobalOptimum z) :
    (leastSquares A b C d weight).IsGlobalOptimum
      ((combined.equiv A b C d weight hweight).backward.map z) :=
  (combined.equiv A b C d weight hweight).map_isGlobalOptimum_backward hz

/-!
## A two-dimensional example

Take `A = I`, `b = (1, 0)`, `λ = 1`, and impose `x₁ + x₂ = 1`.
The solution is `x = (3/4, 1/4)`.
-/

def sample := leastSquares (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] !![1, 1] ![1] 1

def solution : FeasiblePoint sample :=
  ⟨![3 / 4, 1 / 4], by
    norm_num [sample, leastSquares, Fin.sum_univ_two, funext_iff]⟩

example : sample.IsGlobalOptimum solution := by
  intro y
  have balance := congrFun y.property 0
  simp [sample, leastSquares, Fin.sum_univ_two] at balance
  change sample.objective solution.val ≤ sample.objective y.val
  simp [sample, leastSquares, solution, Fin.sum_univ_two, Matrix.one_apply]
  nlinarith [sq_nonneg (y.val 0 - 3 / 4), sq_nonneg (y.val 1 - 1 / 4)]

end
end Examples.Applications.RidgeReg
