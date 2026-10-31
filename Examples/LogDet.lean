/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Certified log-determinant optimization

`Fn.logDet X` means the total real function `Real.log X.det`. Its exact conic
rewrite requires a positive-definite matrix, rather than merely positive
determinant. The lift uses existing PSD and exponential cones.

Each separately supplied domain row is retained and receives its own PSD
witness. Consequently these examples contain that domain block in addition to
the block, exponential family, and scalar bound introduced for the log-det atom.
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

-- Generic negation exchanges the log-det hypograph with this loss epigraph.
def negativeMinimum :=
  problem (X : SymmetricMatrix 2)
    minimize -Fn.logDet X.toMatrix
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

reformulation negativeMinimumConic : negativeMinimum := by
  epigraph t as loss_bound
  conic

#printp negativeMinimumConic

example : GlobalEquivalence negativeMinimum negativeMinimumConic :=
  negativeMinimumConic.equivalence
example : IsConic negativeMinimumConic := negativeMinimumConic.isConic

-- Lowering the domain first leaves an identity-cross-block witness that the
-- later native logarithm/determinant rewrite can use as checked domain evidence.
def nativeMaximum :=
  problem (X : SymmetricMatrix 2)
    maximize Real.log X.toMatrix.det
    subject to
      domain : X.toMatrix.PosDef
      normalization : X.toMatrix.trace = 2

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
