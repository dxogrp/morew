/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Robust regression

Given a matrix `A ∈ ℝᵐˣⁿ`, observations `b ∈ ℝᵐ`, and a threshold `M ≥ 0`,
choose coefficients `x ∈ ℝⁿ` to minimize the Huber loss of the residuals:

```math
\text{minimize}\quad \sum_{i=1}^{m} h_M((Ax-b)_i),
\qquad
h_M(v)=\begin{cases}
v^2,& |v|\leq M\\
2M|v|-M^2,& |v|>M.
\end{cases}
```

For `M > 0`, the loss is quadratic near zero and grows linearly outside that
region, reducing the influence of large residuals. At `M = 0`, it is zero.
-/

namespace Examples.Applications.RobustReg

open Morew
open scoped Matrix
noncomputable section

def regression (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (M : ℝ) :=
  problem (x : Fin n → ℝ)
    let residual := A *ᵥ x - b
    minimize ∑ i, Fn.huber M (residual i)

/-!
Introduce a bound on the total loss, then apply its registered conic representation.
-/

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (M : ℝ) (hM : 0 ≤ M)

include hM in
reformulation conicRegression : (regression A b M) := by
  epigraph t
  conic

#printp conicRegression

example : GlobalEquiv (regression A b M) (conicRegression A b M) :=
  conicRegression.equiv A b M hM
example : IsConic (conicRegression A b M) := conicRegression.isConic A b M
example : (conicRegression.conicForm A b M).data.toProblem = conicRegression A b M :=
  (conicRegression.conicForm A b M).represents

/-!
Recover the coefficients `x` by discarding the bound and auxiliary vectors.
The equivalence certificate transfers global optimality to the regression problem.
-/

example (p : FeasiblePoint (conicRegression A b M)) :
    ((conicRegression.equiv A b M hM).backward.map p).val = p.val.1.1 := rfl

example {p : FeasiblePoint (conicRegression A b M)}
    (hp : (conicRegression A b M).IsGlobalOptimum p) :
    (regression A b M).IsGlobalOptimum
      ((conicRegression.equiv A b M hM).backward.map p) :=
  (conicRegression.equiv A b M hM).map_isGlobalOptimum_backward hp

end
end Examples.Applications.RobustReg
