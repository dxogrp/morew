/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-! Composition of conic and NLP steps through the public commands. -/

namespace MorewTest.Reformulation.NLP

open Morew
noncomputable section

namespace Composition

def source :=
  problem (x : ℝ)
    minimize |x|
    subject to
      square : x ^ 2 ≤ 9
      magnitude : |x| ≤ 2

reformulation mixed : source := by
  conic at square
  nlp at magnitude

def shiftCoverage : FeasibleSurjection mixed (fun y : ℝ => y + 1) where
  preimage x := x.1 - 1
  rightInverse x := by simp

reformulation continued : mixed := by
  substitute x := y + 1 using shiftCoverage
  epigraph t
  nlp at epigraph_t

example : GlobalEquiv source mixed := mixed.equiv
example : GlobalEquiv mixed continued := continued.equiv

def affineSource := problem (x : ℝ) minimize x subject to cap : |x| ≤ 2

reformulation conicTarget : affineSource := by
  nlp at cap
  conic

example : IsConic conicTarget := conicTarget.isConic

end Composition

end
end MorewTest.Reformulation.NLP
