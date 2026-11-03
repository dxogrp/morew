/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

open Morew

/-!
# Power-cone models

Scalar powers, weighted means, geometric means, and inverse products have
exact power-cone formulations. Retained constraints supply nonnegative or
positive base domains. Numeric exponent conditions are checked automatically;
symbolic cone exponents retain their explicit range assumptions.
-/

namespace Examples.Models.Power

noncomputable section

namespace ConvexPower

def source :=
  problem (x : ℝ)
    minimize Real.rpow x (3 / 2)
    subject to
      domain : 0 ≤ x

reformulation ready : source := by
  epigraph t as loss
  conic at loss
  conic

#printp ready

example : GlobalEquivalence source ready := ready.equivalence
example : IsConic ready := ready.isConic

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
example : IsConic ready := ready.isConic

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

#printp ready
example : GlobalEquivalence source ready := ready.equivalence
example : IsConic ready := ready.isConic

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

#printp ready
example : GlobalEquivalence (source α) (ready α) := ready.equivalence α
example : (ready.conicForm α hα).data.toProblem = ready α :=
  (ready.conicForm α hα).represents
example : IsConic (ready α) := ready.isConic α hα

end DirectMembership

namespace GeometricMean

def source :=
  problem (x : Fin 3 → ℝ)
    maximize Fn.geoMean x
    subject to
      domain : 0 ≤ x
      budget : ∑ i, x i ≤ 3

reformulation ready : source := by
  hypograph t as mean
  conic

-- Prefix means connect the coordinates in their original order.
#printp ready
example : GlobalEquivalence source ready := ready.equivalence
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents
example : IsConic ready := ready.isConic

end GeometricMean

namespace InverseProduct

def source :=
  problem (x : Fin 3 → ℝ)
    minimize Fn.invProd x
    subject to
      -- This retained margin proves that every coordinate is strictly positive.
      domain : (fun _ => 1) ≤ x
      budget : ∑ i, x i ≤ 6

reformulation ready : source := by
  epigraph t as inverse
  conic

#printp ready
example : GlobalEquivalence source ready := ready.equivalence
example : ready.conicForm.data.toProblem = ready := ready.conicForm.represents
example : IsConic ready := ready.isConic

end InverseProduct

end
end Examples.Models.Power
