/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Positive semidefinite and positive definite matrix constraints

The first problem has a scalar variable x:

```math
\begin{array}{ll}
\text{minimize} & x \\
\text{subject to} & \operatorname{diag}(x,1) \succeq 0.
\end{array}
```
-/

namespace Examples.Models.PSD

open Morew Morew.Conic
noncomputable section

def diagonalModel :=
  problem (x : ℝ)
    let matrix := Matrix.diagonal ![x, 1]
    minimize x
    subject to
      semidefinite : matrix.PosSemidef

reformulation diagonalConic : diagonalModel := by conic

#printp diagonalConic
example : GlobalEquivalence diagonalModel diagonalConic := diagonalConic.equivalence
example : IsConic diagonalConic := diagonalConic.isConic

/-!
For a symmetric 2 × 2 matrix variable P, the trace problem is

```math
\begin{array}{ll}
\text{minimize} & \operatorname{tr}P \\
\text{subject to} & P \succ 0, \\
 & P \succeq I.
\end{array}
```
-/

def positiveDefiniteModel :=
  problem (P : SymmetricMatrix 2)
    minimize P.toMatrix.trace
    subject to
      domain : P.toMatrix.PosDef
      lower : (P.toMatrix - 1).PosSemidef

reformulation positiveDefiniteConic : positiveDefiniteModel := by conic

#printp positiveDefiniteConic

example : GlobalEquivalence positiveDefiniteModel positiveDefiniteConic :=
  positiveDefiniteConic.equivalence
example : IsConic positiveDefiniteConic := positiveDefiniteConic.isConic

end
end Examples.Models.PSD
