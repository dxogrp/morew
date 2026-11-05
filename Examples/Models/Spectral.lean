/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Matrix and spectral reformulations

Largest eigenvalues, Euclidean operator norms, nuclear norms, and matrix
fractions have semidefinite representations. The first model has a symmetric
2 × 2 matrix variable `A`:

```math
\begin{array}{ll}
\text{minimize} & \lambda_{\max}(A) \\
\text{subject to} & \operatorname{tr}A=1.
\end{array}
```
-/

namespace Examples.Models.Spectral

open Morew Morew.Conic

noncomputable section

def largestEigenvalueModel :=
  problem (A : SymmetricMatrix 2)
    minimize Fn.lambdaMax A.toMatrix
    subject to
      normalization : A.toMatrix.trace = 1

reformulation largestEigenvalueConic : largestEigenvalueModel := by
  epigraph t as largest
  conic

#printp largestEigenvalueConic

example : GlobalEquiv largestEigenvalueModel largestEigenvalueConic :=
  largestEigenvalueConic.equiv
example : IsConic largestEigenvalueConic := largestEigenvalueConic.isConic

/-!
The operator-norm model has a 2 × 3 matrix variable `A`:

```math
\begin{array}{ll}
\text{minimize} & \lVert A\rVert_2 \\
\text{subject to} & A_{11}=1, \quad A_{23}=2.
\end{array}
```
-/

-- The scope selects the Euclidean operator norm in the modeled objective.
open scoped Matrix.Norms.L2Operator in
def operatorNormModel :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize ‖A‖
    subject to
      firstEntry : A 0 0 = 1
      lastEntry : A 1 2 = 2

reformulation operatorNormConic : operatorNormModel := by
  epigraph t as norm_bound
  conic at norm_bound
  conic

#printp operatorNormConic

example : GlobalEquiv operatorNormModel operatorNormConic :=
  operatorNormConic.equiv
example : IsConic operatorNormConic := operatorNormConic.isConic

/-!
For a 2 × 3 matrix variable `A`, nuclear-norm completion is

```math
\begin{array}{ll}
\text{minimize} & \lVert A\rVert_* \\
\text{subject to} & A_{11}=1, \quad A_{22}=1.
\end{array}
```
-/

-- The nuclear-norm bound uses half the sum of two auxiliary matrix traces.
def normNucModel :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize Fn.normNuc A
    subject to
      firstEntry : A 0 0 = 1
      secondEntry : A 1 1 = 1

reformulation normNucConic : normNucModel := by
  epigraph t as nuclear_bound
  conic

#printp normNucConic

example : GlobalEquiv normNucModel normNucConic := normNucConic.equiv
example : IsConic normNucConic := normNucConic.isConic

/-!
The matrix-fraction model has a vector variable `x ∈ ℝ²` and a symmetric
2 × 2 matrix variable `P`:

```math
\begin{array}{ll}
\text{minimize} & x^T P^{-1}x \\
\text{subject to} & P \succ 0, \\
 & \operatorname{tr}P=2, \\
 & x_1=1.
\end{array}
```
-/

def matrixFractionModel :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2)
    minimize Fn.matFrac x P.toMatrix
    subject to
      domain : P.toMatrix.PosDef
      normalization : P.toMatrix.trace = 2
      anchor : x 0 = 1

reformulation matrixFractionConic : matrixFractionModel := by
  epigraph t as fraction_bound
  -- The matrix-fraction rule accepts the semidefinite representation of `P ≻ 0`.
  conic at domain
  conic at fraction_bound
  conic

#printp matrixFractionConic

example : GlobalEquiv matrixFractionModel matrixFractionConic :=
  matrixFractionConic.equiv
example : IsConic matrixFractionConic := matrixFractionConic.isConic

end

end Examples.Models.Spectral
