/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Certified coordinate substitutions

`substitute` replaces a selected coordinate and proves that every feasible
original point has a preimage. The replacement need not be injective: squaring
covers nonnegative values, with the square root as a chosen preimage.

A registered parameterization supplies reusable coverage mathematics; `via`
selects one explicitly. Morew checks its range against the current constraints
and preserves all other coordinates. The existing `using` form instead accepts
a complete, problem-specific `FeasibleSurjection` certificate.
-/

namespace Examples.Substitution

open Morew
noncomputable section

def nonnegative :=
  problem (x : ℝ)
    minimize x
    subject to
      domain : 0 ≤ x
      budget : x ≤ 4

-- The nonnegativity row becomes a proved tautology after squaring.
reformulation squared : nonnegative := by
  substitute x := u ^ 2
  nlp

#printp squared
example : GlobalEquivalence nonnegative squared := squared.equivalence
example : IsSmoothNLP squared := squared.isSmoothNLP

-- `via` chooses a reusable descriptor; the current problem supplies coverage.
reformulation explicitlySquared : nonnegative := by
  substitute x := u ^ 2 via Morew.Substitution.square

example : GlobalEquivalence nonnegative explicitlySquared := explicitlySquared.equivalence

def interval :=
  problem (x : ℝ)
    maximize x
    subject to
      lower : 1 ≤ x
      upper : x ≤ 5

-- Basic affine forms are recognized without a problem-specific certificate.
reformulation affineCoordinates : interval := by
  substitute x := 2 * u + 1
  conic

#printp affineCoordinates
example : GlobalEquivalence interval affineCoordinates := affineCoordinates.equivalence
example : IsConic affineCoordinates := affineCoordinates.isConic

def scaled :=
  problem (a x : ℝ)
    minimize x
    subject to
      slope : 0 < a
      budget : x ≤ 4

-- The slope is a retained decision coordinate. Its nonzero condition follows
-- from source feasibility, and the generated maps leave `a` unchanged.
reformulation retainedCoefficient : scaled := by
  substitute x := a * u

#printp retainedCoefficient
example : GlobalEquivalence scaled retainedCoefficient := retainedCoefficient.equivalence

end
end Examples.Substitution
