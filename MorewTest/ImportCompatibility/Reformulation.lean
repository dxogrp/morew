/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Surface entry-point compatibility

The established narrow import must supply the DSL, built-in steps, certificates,
and problem printer without relying on the library-wide import aggregator.
-/

namespace MorewTest.ImportCompatibility.Reformulation

open Morew
noncomputable section

def source :=
  problem (x : ℝ)
    minimize (Real.log x)^2
    subject to
      positive : 0 < x

reformulation target : source := by
  substitute x := Real.exp u
  epigraph t

example : GlobalEquivalence source target := target.equivalence

example (u t : ℝ) : target.objective (u, t) = t := rfl

example (u t : ℝ) : target.feasible (u, t) ↔ u ^ 2 ≤ t := Iff.rfl

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    epigraph_t : u ^ 2 ≤ t
-/
#guard_msgs in
#printp target

end
end MorewTest.ImportCompatibility.Reformulation
