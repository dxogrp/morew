/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Certified finite power-cone reformulations

Finite p-norms use mathlib's `PiLp` norm. Geometric means and inverse products
use ordinary functions with nonnegative and strictly positive coordinate domains.
Each finite cone family stays grouped, including at symbolic dimensions.

Automatic selection reports ambiguity when multiple exact rules apply. The L2
example shows how `using` chooses either the SOC or power-cone representation.
-/

namespace Examples.PowerFamilies

open Morew
noncomputable section

namespace PNorm

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖WithLp.toLp (3 / 2) x‖ ≤ t

variable (n : ℕ)

reformulation ready : (source n) := by
  conic

-- The exact cone exponent is 2/3, with one auxiliary coordinate per input.
#printp ready
example : GlobalEquivalence (source n) (ready n) := ready.equivalence n
example : (ready.conicForm n).data.toProblem = ready n := (ready.conicForm n).represents
example : IsConic (ready n) := ready.isConic n

end PNorm

namespace L2

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖WithLp.toLp 2 x‖ ≤ t

variable (n : ℕ)

-- Both rules apply at p = 2; omitting `using` reports their ambiguity.
-- SOC uses one cone constraint on (t, x), without an auxiliary vector.
reformulation soc : (source n) := by
  conic at bound using Morew.Conic.SecondOrder.normEpigraph
  conic

#printp soc
example : GlobalEquivalence (source n) (soc n) := soc.equivalence n
example : Conic.Form (soc n) := soc.conicForm n
example : (soc.conicForm n).data.toProblem = soc n := (soc.conicForm n).represents
example : IsConic (soc n) := soc.isConic n

-- The power formulation adds r, with 0 ≤ t, ∑ i, r i ≤ t, and
-- (r i, t, x i) ∈ POW (1/2) for each coordinate.
reformulation power : (source n) := by
  conic at bound using Morew.Conic.Power.normEpigraph
  conic

#printp power
example : GlobalEquivalence (source n) (power n) := power.equivalence n
example : Conic.Form (power n) := power.conicForm n
example : (power.conicForm n).data.toProblem = power n := (power.conicForm n).represents
example : IsConic (power n) := power.isConic n

end L2

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
end Examples.PowerFamilies
