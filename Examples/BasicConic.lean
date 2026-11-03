/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

open Morew

namespace Examples.Basic

/-
Targeted polyhedral rewriting
-/
namespace Polyhedral
noncomputable section

def p :=
  problem (x : ℝ)
    minimize |x - 2|
    subject to
      magnitude : |x| ≤ 5
      nonnegative : 0 ≤ x

reformulation linearBounds : p := by
  conic at magnitude
  epigraph t as distance
  conic at distance

#printp linearBounds
example : GlobalEquivalence p linearBounds := linearBounds.equivalence

end
end Polyhedral

end Examples.Basic
