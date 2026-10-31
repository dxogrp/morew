/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Certified log-determinant optimization

`Fn.logDet X` means the total real function `Real.log X.det`.
Its exact conic rewrite requires a positive-definite matrix.
The lift uses existing PSD and exponential cones.
-/

namespace Morew.Examples.LogDet

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

-- The same objective can use native `Real.log` and `Matrix.det` directly.
def nativeMaximum :=
  problem (X : SymmetricMatrix 2)
    maximize Real.log X.toMatrix.det
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

/-
This example lowers the domain first to demonstrate that either rewrite order
is supported. The explicit early `conic at domain` step is optional: the log-det
rule can use the original `PosDef` constraint directly, or recover positive
definiteness from its retained PSD witness after domain lowering.
-/
reformulation domainFirstConic : nativeMaximum := by
  hypograph t as logDet_bound
  conic at domain
  conic at logDet_bound using Morew.Conic.LogDet.nativeHypograph
  conic

#printp domainFirstConic

example : GlobalEquivalence nativeMaximum domainFirstConic := domainFirstConic.equivalence
example : IsConic domainFirstConic := domainFirstConic.isConic

end
end Morew.Examples.LogDet
