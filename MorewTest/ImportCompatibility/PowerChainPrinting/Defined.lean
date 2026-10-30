/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Two exported chains with independent labels and retained constraints -/

namespace MorewTest.ImportCompatibility.PowerChainPrinting.Defined

open Morew
noncomputable section

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (s t : ℝ)
    minimize t
    subject to
      domain : (fun _ => (1 : ℝ)) ≤ x
      floorRow : s ≤ Fn.geoMean x
      ceilingRow : Fn.invProd x ≤ t
      budget : ∑ i, x i ≤ 10
      remaining : |t| ≤ 5

variable (n : ℕ) (hn : 0 < n)

include hn in
reformulation lowered : (source n) := by
  conic at floorRow
  conic at ceilingRow

set_option pp.proofs true in
include hn in
reformulation registeredDetailed : (source n) := by
  conic at floorRow
  conic at ceilingRow

example : GlobalEquivalence (source n) (lowered n hn) := lowered.equivalence n hn

end
end MorewTest.ImportCompatibility.PowerChainPrinting.Defined
