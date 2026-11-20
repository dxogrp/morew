/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic

/-!
# Log-sum-exp with a Euclidean bound

Given matrices `A ∈ ℝᵐˣⁿ`, `B ∈ ℝᵏˣⁿ`, vectors `b ∈ ℝᵐ`, `d ∈ ℝᵏ`,
and a radius `R ∈ ℝ`, choose `x ∈ ℝⁿ` to solve

```math
\begin{array}{ll}
\text{minimize} & \log\!\left(\sum_{i=1}^{m}\exp((Ax+b)_i)\right) \\
\text{subject to} & \lVert Bx-d\rVert_2\leq R.
\end{array}
```

Assume `m > 0`, so the sum inside the logarithm is positive.
-/

@[expose] public section

namespace Examples.Models.LogSumExp

open Morew Morew.Conic
open scoped Matrix
noncomputable section

def source (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (B : Matrix (Fin k) (Fin n) ℝ) (d : Fin k → ℝ) (R : ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.logSumExp (A *ᵥ x + b)
    subject to
      radius : Fn.norm2 (B *ᵥ x - d) ≤ R

/-!
Introduce an upper bound `t` on the objective, and minimize `t`. The log-sum-exp
epigraph representation uses the assumption `m > 0` and introduces an auxiliary
vector `u ∈ ℝᵐ` satisfying

```math
((Ax+b)_i-t,1,u_i)\in\mathrm{EXP}\quad(i=1,\ldots,m),
\qquad \mathbf{1}^T u\leq1.
```

Each exponential-cone constraint is equivalent to `exp((Ax+b)ᵢ-t) ≤ uᵢ`.
If the objective is at most `t`, setting `uᵢ = exp((Ax+b)ᵢ-t)` satisfies these
constraints and the sum bound. Conversely, these constraints imply
`∑ᵢ exp((Ax+b)ᵢ) ≤ exp(t)`, so the objective is at most `t`.

Finally, `conic` represents the Euclidean norm constraint and the sum inequality by

```math
(R,Bx-d)\in\mathrm{SOC}_k,\qquad 1-\mathbf{1}^T u\in\mathbf{R}_+.
```
-/

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
  (B : Matrix (Fin k) (Fin n) ℝ) (d : Fin k → ℝ) (R : ℝ) (hm : 0 < m)

reformulation conicTarget : (source A b B d R) := by
  epigraph t as loss
  conic at loss
  conic

#printp conicTarget

example : GlobalEquiv (source A b B d R) (conicTarget A b B d R) :=
  conicTarget.equiv A b B d R hm
example : IsConic (conicTarget A b B d R) := conicTarget.isConic A b B d R

example : (conicTarget.conicForm A b B d R).data.toProblem = conicTarget A b B d R :=
  (conicTarget.conicForm A b B d R).represents

example (x : Fin n → ℝ) (t : ℝ) (u : Fin m → ℝ) :
    (conicTarget A b B d R).objective ((x, t), u) = t := rfl

example (x : Fin n → ℝ) (t : ℝ) (u : Fin m → ℝ) :
    (conicTarget A b B d R).feasible ((x, t), u) ↔
      (R, B *ᵥ x - d) ∈ SOC k ∧
      (∀ i, ((A *ᵥ x + b) i - t, 1, u i) ∈ EXP) ∧
      1 - ∑ i, u i ∈ ℝ₊ := Iff.rfl

/-!
The recovery map sends a feasible target point `((x,t),u)` to `x`.
The equivalence certificate transfers global optimality to the source problem.
-/

example (z : FeasiblePoint (conicTarget A b B d R)) :
    ((conicTarget.equiv A b B d R hm).backward.map z).val = z.val.1.1 := rfl

/-!
If `R < 0`, nonnegativity of the Euclidean norm implies that the source problem
is infeasible. The recovery map then implies that the target problem is also
infeasible.
-/

example (hR : R < 0) : ¬ (source A b B d R).HasFeasiblePoint := by
  rintro ⟨x⟩
  exact (not_le_of_gt hR) ((Fn.norm2_nonneg (B *ᵥ x.val - d)).trans x.property)

example (hR : R < 0) : ¬ (conicTarget A b B d R).HasFeasiblePoint := by
  rintro ⟨z⟩
  let x := (conicTarget.equiv A b B d R hm).backward.map z
  exact (not_le_of_gt hR) ((Fn.norm2_nonneg (B *ᵥ x.val - d)).trans x.property)

end
end Examples.Models.LogSumExp
