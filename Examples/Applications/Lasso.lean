/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic

/-!
# LASSO

Given a matrix `A ∈ ℝᵐˣⁿ`, observations `b ∈ ℝᵐ`, and a weight `λ ≥ 0`,
choose coefficients `x ∈ ℝⁿ` to solve

```math
\text{minimize}\quad \lVert Ax-b\rVert_2^2 + \lambda\lVert x\rVert_1.
```
-/

@[expose] public section

namespace Examples.Applications.Lasso

open Morew
open scoped Matrix
noncomputable section

def source (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (lam : ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm2 (A *ᵥ x - b) ^ 2 + lam * Fn.norm1 x

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)

/-!
## Quadratic conic formulation

Introduce a scalar `r` with `‖x‖₁ ≤ r` and replace the regularization term by
`λr`. Since `λ ≥ 0`, the new objective is nondecreasing in `r`. The command
`qconic` retains the quadratic objective and represents the norm bound using
an auxiliary vector `u ∈ ℝⁿ`:

```math
\begin{array}{ll}
\text{minimize} & \lVert Ax-b\rVert_2^2 + \lambda r \\
\text{subject to} & x \preceq u,\quad -x \preceq u, \\
 & \mathbf{1}^T u \leq r.
\end{array}
```

For each `x`, setting `uᵢ = |xᵢ|` and `r = ‖x‖₁` satisfies these constraints
and gives the same objective value as the source problem.
-/

reformulation quadraticTarget : (source A b lam) := by
  epigraph r at (Fn.norm1 x) as regularizer
  qconic

#printp quadraticTarget

example : GlobalEquiv (source A b lam) (quadraticTarget A b lam) :=
  quadraticTarget.equiv A b lam hlam
example : IsQuadConic (quadraticTarget A b lam) := quadraticTarget.isQuadConic A b lam

/-!
The generated `quadConicForm` stores the quadratic and affine parts of the
objective and the cone constraints. Its `represents` certificate proves that
`data.toProblem` equals `quadraticTarget`.
-/

example : (quadraticTarget.quadConicForm A b lam).data.toProblem = quadraticTarget A b lam :=
  (quadraticTarget.quadConicForm A b lam).represents
example (x u : Fin n → ℝ) (r : ℝ) :
    (quadraticTarget A b lam).objective ((x, r), u) =
      Fn.norm2 (A *ᵥ x - b) ^ 2 + lam * r := rfl
example (x u : Fin n → ℝ) (r : ℝ) :
    (quadraticTarget A b lam).feasible ((x, r), u) ↔
      x ≤ u ∧ -x ≤ u ∧ ∑ i, u i ≤ r := by
  change (0 ≤ u - x ∧ 0 ≤ u + x ∧ 0 ≤ r - ∑ i, u i) ↔ _
  simp only [← sub_neg_eq_add, sub_nonneg]

/-!
## Affine conic formulation

Retain the linear constraints of the quadratic conic formulation and introduce
`‖Ax-b‖₂² ≤ t`. The objective is `t + λr`, and the additional constraint is

```math
(t,\tfrac12,Ax-b) \in \mathrm{RSOC}_m.
```
-/

reformulation conicTarget : (source A b lam) := by
  epigraph r at (Fn.norm1 x) as regularizer
  epigraph t at (Fn.norm2 (A *ᵥ x - b) ^ 2) as loss
  conic

#printp conicTarget

example : GlobalEquiv (source A b lam) (conicTarget A b lam) :=
  conicTarget.equiv A b lam hlam
example : IsConic (conicTarget A b lam) := conicTarget.isConic A b lam
example : (conicTarget.conicForm A b lam).data.toProblem = conicTarget A b lam :=
  (conicTarget.conicForm A b lam).represents
example (x u : Fin n → ℝ) (r t : ℝ) :
    (conicTarget A b lam).objective (((x, r), t), u) = t + lam * r := rfl
example (x u : Fin n → ℝ) (r t : ℝ) :
    (conicTarget A b lam).feasible (((x, r), t), u) ↔
      x ≤ u ∧ -x ≤ u ∧ ∑ i, u i ≤ r ∧
      (t, 1 / 2, A *ᵥ x - b) ∈ (Conic.Cone.rotatedSecondOrder m).carrier := by
  change (0 ≤ u - x ∧ 0 ≤ u + x ∧ 0 ≤ r - ∑ i, u i ∧ _) ↔ _
  simp only [← sub_neg_eq_add, sub_nonneg]

/-!
## Recovery

Both recovery maps send a feasible target point to its coefficient vector `x`.
-/

example (z : FeasiblePoint (quadraticTarget A b lam)) :
    ((quadraticTarget.equiv A b lam hlam).backward.map z).val = z.val.1.1 := rfl
example (z : FeasiblePoint (conicTarget A b lam)) :
    ((conicTarget.equiv A b lam hlam).backward.map z).val = z.val.1.1.1 := rfl

end
end Examples.Applications.Lasso
