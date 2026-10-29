/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import Morew.Conic.Power.GeometricMean

/-!
# Exported finite power-family presentations

A symbolic nonempty dimension and its checked chain indices cross the module
boundary, together with the original named functions and retained domain row.
-/

namespace MorewTest.ImportCompatibility.PowerFamilies.Defined

open Morew
noncomputable section

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : (fun _ => (1 : ℝ)) ≤ x
      mean : 0 ≤ Fn.geoMean x
      reciprocal : Fn.invProd x ≤ t
      remaining : |t| ≤ 5

variable (n : ℕ) (hn : 0 < n)

include hn in
reformulation lowered : (source n) := by
  conic at reciprocal

example : GlobalEquivalence (source n) (lowered n hn) := lowered.equivalence n hn

end
end MorewTest.ImportCompatibility.PowerFamilies.Defined
