/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Log-determinant optimization

We maximize the log-determinant over symmetric 2 × 2 matrices X:

```math
\begin{array}{ll}
\text{maximize} & \log\det X \\
\text{subject to} & \operatorname{tr}X=2, \\
 & X \succ 0.
\end{array}
```

The reformulation uses positive semidefinite and exponential cones.
-/

namespace Examples.Models.LogDet

open Morew Morew.Conic

noncomputable section

def maximum :=
  problem (X : SymmetricMatrix 2)
    maximize Fn.logDet X.toMatrix
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

reformulation maximumConic : maximum := by
  hypograph t as logDet_bound
  conic

#printp maximumConic

example : GlobalEquivalence maximum maximumConic := maximumConic.equivalence
example : IsConic maximumConic := maximumConic.isConic
example : maximumConic.conicForm.data.rowCount = 5 := rfl

-- The conic log-determinant constraints imply X ≻ 0, so the domain row is redundant.
reformulation maximumWithoutDomainConic : maximum := by
  hypograph t as logDet_bound
  conic at logDet_bound
  remove at domain using (by
    intro point retained
    exact ((Morew.Conic.LogDet.hypograph_iff point.1.1.toMatrix point.1.2
      (by decide)).mpr ⟨point.2.1, point.2.2, retained.2⟩).1)
  conic

#printp maximumWithoutDomainConic

example : GlobalEquivalence maximum maximumWithoutDomainConic :=
  maximumWithoutDomainConic.equivalence
example : IsConic maximumWithoutDomainConic := maximumWithoutDomainConic.isConic
example : maximumWithoutDomainConic.conicForm.data.rowCount = 4 := rfl
example : maximumWithoutDomainConic.conicForm.data.toProblem = maximumWithoutDomainConic :=
  maximumWithoutDomainConic.conicForm.represents

-- The same objective can use native `Real.log` and `Matrix.det` directly.
def nativeMaximum :=
  problem (X : SymmetricMatrix 2)
    maximize Real.log X.toMatrix.det
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

-- The log-determinant rule also accepts the semidefinite representation of X ≻ 0.
reformulation domainFirstConic : nativeMaximum := by
  hypograph t as logDet_bound
  conic at domain
  conic at logDet_bound using Morew.Conic.LogDet.nativeHypograph
  conic

#printp domainFirstConic

example : GlobalEquivalence nativeMaximum domainFirstConic := domainFirstConic.equivalence
example : IsConic domainFirstConic := domainFirstConic.isConic

end
end Examples.Models.LogDet
