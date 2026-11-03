/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Log-determinant optimization

`Fn.logDet X` means the total real function `Real.log X.det`.
Its conic representation requires a positive-definite matrix. Three variants
maximize it at a fixed trace using PSD and exponential cones. Removing a
redundant domain constraint reduces the row count from five to four.
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

-- The log-det bound's PSD and EXP rows imply positive definiteness. Removing
-- the redundant domain row saves its separate PSD block and auxiliary.
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

/-
Rewrite the domain first. The log-det rule can use either the original
`PosDef` constraint or its semidefinite representation to prove positive definiteness.
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
end Examples.Models.LogDet
