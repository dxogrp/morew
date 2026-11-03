/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Certified log-determinant optimization

`Fn.logDet X` means the total real function `Real.log X.det`.
Maximizing it at a fixed trace requires a positive-definite domain for the
exact conic rewrite. Three certified variants use PSD and exponential cones;
removing the redundant domain constraint reduces the row count from five to four.
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

-- Rewriting the log-det bound first makes the original domain row redundant:
-- the PSD and EXP rows already imply positive definiteness. Removing that row
-- avoids the additional PSD block and auxiliary used by its separate representation.
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
This example rewrites the domain first to demonstrate that either rewrite order
is supported. The explicit early `conic at domain` step is optional: the log-det
rule can use the original `PosDef` constraint directly, or recover positive
definiteness from its retained PSD representation.
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
