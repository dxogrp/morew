/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

open Morew

/-!
# Exact power-cone reformulations

Real exponents remain exact. Numeric range conditions are checked automatically;
symbolic exponents use independent hypotheses such as `hp : 1 < p`.
Base-domain evidence comes from retained constraints. General vector powers and
finite families of power cones are outside the scalar rules shown here.
-/

namespace Examples.Power

noncomputable section

namespace ConvexPower

def source :=
  problem (x : ℝ)
    minimize Real.rpow x (3 / 2)
    subject to
      domain : 0 ≤ x

reformulation ready : source := by
  epigraph t as loss
  -- `at` selects the whole bound; `using` selects this exact representation.
  conic at loss using Conic.Power.rpowEpigraph
  -- Bare `conic` certifies the complete problem and emits its conic form.
  conic

#printp ready

example : GlobalEquivalence source ready := ready.equivalence
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents

end ConvexPower

namespace WeightedMean

def source :=
  problem (x y t : ℝ)
    maximize t
    subject to
      x_domain : 0 ≤ x
      y_domain : 0 ≤ y
      budget : x + y ≤ 10
      gain : t ≤ x ^ (1 / 3 : ℝ) * y ^ (1 - (1 / 3 : ℝ))

reformulation ready : source := by
  -- A nonnegative auxiliary preserves this bound even when t is negative.
  conic at gain
  conic

#printp ready

example : GlobalEquivalence source ready := ready.equivalence
example : ready.conicForm.data.sense = .maximize := rfl

end WeightedMean

namespace NegativePower

def source :=
  problem (x t : ℝ)
    minimize t
    subject to
      -- Negative powers require a strictly positive base, certified by this margin.
      domain : 1 ≤ x
      bound : x ^ (-1 / 2 : ℝ) ≤ t

reformulation ready : source := by
  conic

example : GlobalEquivalence source ready := ready.equivalence

end NegativePower

namespace DirectMembership

def source (α : ℝ) :=
  problem (x y z : ℝ)
    maximize z
    subject to
      cone : (x, y, z) ∈ POW α
      budget : x + y ≤ 1

variable (α : ℝ) (hα : 0 < α ∧ α < 1)

-- The range proof is retained by the certificate without appearing in POW α.
include hα in
reformulation ready : (source α) := by
  conic

example : (ready.conicForm α hα).data.toProblem = ready α :=
  (ready.conicForm α hα).represents

end DirectMembership

end
end Examples.Power
