/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

open Morew

/-!
# Power-cone models

Scalar powers, weighted and geometric means, and inverse products have
power-cone formulations. Base domains come from the constraints; symbolic
exponents require a proof of `0 < α ∧ α < 1`.
-/

namespace Examples.Models.Power

noncomputable section

/-!
A convex power of a scalar variable x:

```math
\begin{array}{ll}
\text{minimize} & x^{3/2} \\
\text{subject to} & x \geq 0.
\end{array}
```
-/

namespace ConvexPower

def source :=
  problem (x : ℝ)
    minimize Real.rpow x (3 / 2)
    subject to
      domain : 0 ≤ x

reformulation ready : source := by
  epigraph t as loss
  conic at loss
  conic

#printp ready

example : GlobalEquivalence source ready := ready.equivalence
example : IsConic ready := ready.isConic

end ConvexPower

/-!
A weighted geometric mean with scalar variables x, y, and t:

```math
\begin{array}{ll}
\text{maximize} & t \\
\text{subject to} & t \leq x^{1/3}y^{2/3}, \\
 & x+y \leq 10, \\
 & x \geq 0, \quad y \geq 0.
\end{array}
```
-/

namespace WeightedMean

def source :=
  problem (x y t : ℝ)
    maximize t
    subject to
      x_domain : 0 ≤ x
      y_domain : 0 ≤ y
      budget : x + y ≤ 10
      gain : t ≤ x ^ (1 / 3 : ℝ) * y ^ (1 - (1 / 3 : ℝ))

reformulation ready : source := by
  -- A nonnegative auxiliary preserves this bound even when t is negative.
  conic at gain
  conic

#printp ready

example : GlobalEquivalence source ready := ready.equivalence
example : IsConic ready := ready.isConic

end WeightedMean

/-!
A negative power with scalar variables x and t:

```math
\begin{array}{ll}
\text{minimize} & t \\
\text{subject to} & x^{-1/2} \leq t, \\
 & x \geq 1.
\end{array}
```
-/

namespace NegativePower

def source :=
  problem (x t : ℝ)
    minimize t
    subject to
      -- The negative power requires x > 0.
      domain : 1 ≤ x
      bound : x ^ (-1 / 2 : ℝ) ≤ t

reformulation ready : source := by
  conic

#printp ready
example : GlobalEquivalence source ready := ready.equivalence
example : IsConic ready := ready.isConic

end NegativePower

/-!
For 0 < α < 1, direct power-cone membership gives the scalar problem

```math
\begin{array}{ll}
\text{maximize} & z \\
\text{subject to} & |z| \leq x^\alpha y^{1-\alpha}, \\
 & x+y \leq 1, \\
 & x \geq 0, \quad y \geq 0.
\end{array}
```
-/

namespace DirectMembership

def source (α : ℝ) :=
  problem (x y z : ℝ)
    maximize z
    subject to
      cone : (x, y, z) ∈ POW α
      budget : x + y ≤ 1

variable (α : ℝ) (hα : 0 < α ∧ α < 1)

-- Include the exponent range in the conic certificate.
include hα in
reformulation ready : (source α) := by
  conic

#printp ready
example : GlobalEquivalence (source α) (ready α) := ready.equivalence α
example : (ready.conicForm α hα).data.toProblem = ready α :=
  (ready.conicForm α hα).represents
example : IsConic (ready α) := ready.isConic α hα

end DirectMembership

/-!
The geometric-mean model has variable x ∈ ℝ³:

```math
\begin{array}{ll}
\text{maximize} & (x_1x_2x_3)^{1/3} \\
\text{subject to} & \mathbf{1}^T x \leq 3, \\
 & x \succeq 0.
\end{array}
```
-/

namespace GeometricMean

def source :=
  problem (x : Fin 3 → ℝ)
    maximize Fn.geoMean x
    subject to
      domain : 0 ≤ x
      budget : ∑ i, x i ≤ 3

reformulation ready : source := by
  hypograph t as mean
  conic

/-! Prefix means connect the coordinates in their original order. -/
#printp ready
example : GlobalEquivalence source ready := ready.equivalence
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents
example : IsConic ready := ready.isConic

end GeometricMean

/-!
The inverse-product model has variable x ∈ ℝ³:

```math
\begin{array}{ll}
\text{minimize} & 1/(x_1x_2x_3) \\
\text{subject to} & \mathbf{1}^T x \leq 6, \\
 & x \succeq \mathbf{1}.
\end{array}
```
-/

namespace InverseProduct

def source :=
  problem (x : Fin 3 → ℝ)
    minimize Fn.invProd x
    subject to
      -- The inverse product requires positive coordinates.
      domain : (fun _ => 1) ≤ x
      budget : ∑ i, x i ≤ 6

reformulation ready : source := by
  epigraph t as inverse
  conic

#printp ready
example : GlobalEquivalence source ready := ready.equivalence
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents
example : IsConic ready := ready.isConic

end InverseProduct

end
end Examples.Models.Power
