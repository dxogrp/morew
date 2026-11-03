/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Certified coordinate substitutions

`substitute` replaces a selected coordinate and proves that every feasible
original point has a preimage. Domain constraints justify the square and
exponential substitutions below. Each script records global equivalence;
scripts ending in `conic` or `nlp` also certify the complete resulting form.
-/

namespace Examples.Transformations.Substitution

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

-- Without `via`, Morew searches the registered substitution rules. Here `via`
-- selects only `Morew.Substitution.square`, with no fallback to another rule.
-- In contrast, `using` supplies a complete problem-specific `FeasibleSurjection`.
reformulation explicitlySquared : nonnegative := by
  substitute x := u ^ 2 via Morew.Substitution.square

-- This example intentionally stops at the substitution and its equivalence.
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

-- A substitution can depend on another decision variable: here its coefficient
-- is `a`. The source constraint `0 < a` guarantees `a ≠ 0`, so every feasible
-- original point has a preimage with `u = x / a`. Both the substitution
-- `(a, u) ↦ (a, a * u)` and the chosen preimage `(a, x) ↦ (a, x / a)` preserve `a`.
reformulation retainedCoefficient : scaled := by
  substitute x := a * u

#printp retainedCoefficient
example : GlobalEquivalence scaled retainedCoefficient := retainedCoefficient.equivalence

namespace LogSquared

def p :=
  problem (x : ℝ)
    minimize (Real.log x) ^ 2
    subject to
      positive : 0 < x

#printp p

-- Positivity makes x = exp u a surjective parameterization of feasible x.
-- The objective becomes u², whose epigraph is the intermediate problem.
reformulation exponentialEpigraph : p := by
  substitute x := Real.exp u
  epigraph t

#printp exponentialEpigraph
example : GlobalEquivalence p exponentialEpigraph := exponentialEpigraph.equivalence

-- The final step represents the quadratic bound with a cone and certifies
-- the complete problem.
reformulation conicProb : p := by
  substitute x := Real.exp u
  epigraph t
  conic

#printp conicProb
example : GlobalEquivalence p conicProb := conicProb.equivalence
example : IsConic conicProb := conicProb.isConic

end LogSquared

end
end Examples.Transformations.Substitution
