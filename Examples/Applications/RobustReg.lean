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
v^2,& |v|\leq M,\\
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
## Conic formulation

Introduce an upper bound `t` on the objective. For each residual `v`, the identity

```math
h_M(v)=\min_z\bigl(z^2+2M|v-z|\bigr)
```

is attained at `z = max(-M, min(M, v))`. Collect these values in `z ∈ ℝᵐ`
and introduce `u ∈ ℝᵐ` bounding the absolute deviations. Summing the scalar
representations gives

```math
\begin{array}{ll}
\text{minimize} & t\\
\text{subject to} & \lVert z\rVert_2^2+2M\mathbf{1}^Tu\leq t,\\
& -u\preceq Ax-b-z\preceq u.
\end{array}
```

The first inequality is the rotated second-order cone constraint
`(t - 2M𝟙ᵀu, 1/2, z) ∈ RSOC m`. The other two inequalities are componentwise.
The assumption `M ≥ 0` allows replacing absolute deviations by upper bounds
without decreasing their weighted sum.
The following representation proves both directions and supplies the attained
values when lifting a feasible point.
-/

def regressionEpigraph (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : ℝ) (hM : 0 ≤ M) :
    EpigraphRepr (fun x : Fin n → ℝ => ∑ i, Fn.huber M ((A *ᵥ x - b) i)) where
  Auxiliary := (Fin m → ℝ) × (Fin m → ℝ)
  target x t p :=
    (t - 2 * M * (∑ i, p.2 i), 1 / 2, p.1) ∈
        (Conic.Cone.rotatedSecondOrder m).carrier ∧
      -p.2 ≤ A *ᵥ x - b - p.1 ∧ A *ᵥ x - b - p.1 ≤ p.2
  source_iff_exists x t := by
    let e := A *ᵥ x - b
    constructor
    · intro ht
      let z : Fin m → ℝ := fun i => max (-M) (min M (e i))
      let u : Fin m → ℝ := fun i => |e i - z i|
      have hvalue : (∑ i, Fn.huber M (e i)) =
          (∑ i, z i ^ 2) + 2 * M * (∑ i, u i) := by
        calc
          _ = ∑ i, (z i ^ 2 + 2 * M * u i) :=
            Finset.sum_congr rfl fun i _ => Fn.huber_eq_square_add_abs_clamp M (e i) hM
          _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      refine ⟨(z, u), ?_, ?_, ?_⟩
      · apply (Conic.SecondOrder.sumSquares_le_iff z _).mp
        change (∑ i, Fn.huber M (e i)) ≤ t at ht
        rw [hvalue] at ht
        linarith
      · intro i
        exact neg_abs_le (e i - z i)
      · intro i
        exact le_abs_self (e i - z i)
    · rintro ⟨⟨z, u⟩, hcone, hlower, hupper⟩
      have hsquare := (Conic.SecondOrder.sumSquares_le_iff z _).mpr hcone
      have hbound (i : Fin m) : Fn.huber M (e i) ≤ z i ^ 2 + 2 * M * u i := by
        have habs : |e i - z i| ≤ u i := abs_le.mpr ⟨hlower i, hupper i⟩
        calc
          _ ≤ z i ^ 2 + 2 * M * |e i - z i| :=
            Fn.huber_le_square_add_abs M (e i) (z i) hM
          _ ≤ _ := add_le_add le_rfl
            (mul_le_mul_of_nonneg_left habs
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM))
      have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hbound i
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
      change (∑ i, Fn.huber M (e i)) ≤ t
      linarith

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (M : ℝ) (hM : 0 ≤ M)

reformulation conicRegression : (regression A b M) := by
  epigraph t as lossBound
  conic at lossBound using (regressionEpigraph A b M hM)
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

/-! A zero threshold or an empty set of observations gives a zero objective. -/

example (x : Fin n → ℝ) : (regression A b 0).objective x = 0 := by
  simp [regression]

example (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) (x : Fin n → ℝ) :
    (regression A b M).objective x = 0 := by
  simp [regression]

end
end Examples.Applications.RobustReg
