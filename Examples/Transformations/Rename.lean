/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Naming constraints during a reformulation

`rename old to new` changes a current label in place. Later steps
select the new label; the predicate and its position stay the same.
-/

namespace Examples.Transformations.Rename

open Morew
noncomputable section

def bounded :=
  problem (x : ℝ)
    minimize x
    subject to magnitude : |x| ≤ 3

-- Choose a name before rewriting a row, then name its generated pieces.
reformulation interval : bounded := by
  rename magnitude to cap
  conic at cap
  rename cap_conic_1 to upper
  rename cap_conic_2 to lower

#printp interval
example (x : ℝ) : interval.feasible x ↔ x ≤ 3 ∧ -x ≤ 3 := Iff.rfl
example : GlobalEquivalence bounded interval := interval.equivalence

def logarithmic :=
  problem (x : ℝ)
    maximize Real.log x
    subject to
      positive : 0 < x
      cap : x ≤ 3

reformulation exponential : logarithmic := by
  -- Renaming the domain row does not interfere with its later removal.
  rename positive to domain
  substitute x := Real.exp u
  rename cap to upper
  hypograph t as value_bound
  rename value_bound to objective_bound

#printp exponential
example : GlobalEquivalence logarithmic exponential := exponential.equivalence

end
end Examples.Transformations.Rename
