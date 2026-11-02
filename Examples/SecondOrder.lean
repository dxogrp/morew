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

/-
Nonnegative least squares
-/
namespace NonnegLS

open scoped Matrix

noncomputable def nonnegLS (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize ‖WithLp.toLp 2 (A *ᵥ x - b)‖
    subject to
      nonneg : x ≥ 0

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

reformulation conicNonnegLS : (nonnegLS A b) := by
  epigraph t as residualBound
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic

noncomputable example : GlobalEquivalence (nonnegLS A b) (conicNonnegLS A b) :=
  conicNonnegLS.equivalence A b

#printp conicNonnegLS

end NonnegLS

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
