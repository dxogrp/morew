/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Second-order cone models

Nonnegative least squares and a quadratic-over-linear objective admit exact
second-order cone formulations. The quotient model retains a positive lower
bound on its denominator; both scripts finish with conic certification.
-/

open Morew

namespace Examples.Models.SecondOrder

namespace NonnegLS

open scoped Matrix

-- ANCHOR: nonnegLS
noncomputable def nonnegLS (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm2 (A *ᵥ x - b)
    subject to
      nonneg : x ≥ 0
-- ANCHOR_END: nonnegLS

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

-- ANCHOR: conicNonnegLS
reformulation conicNonnegLS : (nonnegLS A b) := by
  epigraph t as residualBound
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic
-- ANCHOR_END: conicNonnegLS

-- ANCHOR: nonnegLSCertificate
noncomputable example : GlobalEquivalence (nonnegLS A b) (conicNonnegLS A b) :=
  conicNonnegLS.equivalence A b
example : IsConic (conicNonnegLS A b) := conicNonnegLS.isConic A b
-- ANCHOR_END: nonnegLSCertificate

-- ANCHOR: printNonnegLS
/-! Print the conic problem. -/
#printp conicNonnegLS
-- ANCHOR_END: printNonnegLS

end NonnegLS

namespace QuadraticOverLinear
noncomputable section

def p :=
  problem (x y : ℝ)
    minimize x ^ 2 / y
    subject to
      -- Denominator bound certifies positivity for the quotient rewrite.
      denominator : 1 ≤ y

reformulation quotientConic : p := by
  epigraph t as quadraticBound
  conic at quadraticBound
  conic

#printp p
#printp quotientConic
example : GlobalEquivalence p quotientConic := quotientConic.equivalence
example : IsConic quotientConic := quotientConic.isConic

end
end QuadraticOverLinear

end Examples.Models.SecondOrder
