/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

-- ANCHOR: nonnegLSSetup
import Morew.Reformulation.Conic
open Morew
open scoped Matrix
-- ANCHOR_END: nonnegLSSetup

/-!
# Second-order cone models

For a given m × n matrix A and vector b ∈ ℝᵐ, nonnegative least squares
in norm form is

```math
\begin{array}{ll}
\text{minimize} & \lVert Ax-b\rVert_2 \\
\text{subject to} & x \succeq 0,
\end{array}
```

with variable x ∈ ℝⁿ and componentwise inequality.
-/

namespace Examples.Models.SecondOrder

namespace NonnegLS

-- ANCHOR: nonnegLS
noncomputable def nonnegLS (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm2 (A *ᵥ x - b)
    subject to
      nonneg : x ≥ 0
-- ANCHOR_END: nonnegLS

-- ANCHOR: conicNonnegLS
variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

reformulation conicNonnegLS : (nonnegLS A b) := by
  epigraph t as residualBound
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic
-- ANCHOR_END: conicNonnegLS

-- ANCHOR: nonnegLSCertificate
noncomputable example : GlobalEquivalence (nonnegLS A b) (conicNonnegLS A b) :=
  conicNonnegLS.equivalence A b
example : IsConic (conicNonnegLS A b) := conicNonnegLS.isConic A b
-- ANCHOR_END: nonnegLSCertificate

-- ANCHOR: printNonnegLS
#printp conicNonnegLS
-- ANCHOR_END: printNonnegLS

end NonnegLS

namespace QuadraticOverLinear
noncomputable section

/-!
The quadratic-over-linear model has scalar variables x and y:

```math
\begin{array}{ll}
\text{minimize} & x^2/y \\
\text{subject to} & y \geq 1.
\end{array}
```
-/

def p :=
  problem (x y : ℝ)
    minimize x ^ 2 / y
    subject to
      denominator : 1 ≤ y

reformulation quotientConic : p := by
  epigraph t as quadraticBound
  conic at quadraticBound
  conic

#printp p
#printp quotientConic
example : GlobalEquivalence p quotientConic := quotientConic.equivalence
example : IsConic quotientConic := quotientConic.isConic

end
end QuadraticOverLinear

end Examples.Models.SecondOrder
