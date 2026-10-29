/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

open Morew

/-
Second-order cone rewriting
-/
namespace Examples.SecondOrder

namespace NormBound
noncomputable section

def p :=
  problem (x : Fin 2 → ℝ)
    minimize (x 0 - 1) ^ 2 + (x 1 + 2) ^ 2
    subject to
      radius : ‖WithLp.toLp 2 x‖ ≤ 5

reformulation coneBound : p := by
  conic at radius
  epigraph t as objectiveBound

#printp coneBound
example : GlobalEquivalence p coneBound := coneBound.equivalence

end
end NormBound

namespace QuadraticOverLinear
noncomputable section

def p :=
  problem (x y : ℝ)
    minimize x ^ 2 / y
    subject to
      -- Denominator bound certifies positivity for the quotient rewrite.
      denominator : 1 ≤ y

reformulation lowered : p := by
  epigraph t as quadraticBound
  conic at quadraticBound

#printp p
#printp lowered
example : GlobalEquivalence p lowered := lowered.equivalence

end
end QuadraticOverLinear

end Examples.SecondOrder
