/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic

/-!
# Problems, epigraphs, and optimality certificates

A `problem` specifies its variables, objective, and constraints. A `reformulation`
constructs an equivalent problem and maps feasible points and global optima
between the two. We begin with the scalar problem:

```math
\begin{array}{ll}
\text{minimize} & x^2 \\
\text{subject to} & x \geq 0.
\end{array}
```
-/

open Morew
open Real

namespace Examples.GettingStarted.Basic

namespace Epigraph
noncomputable

def p :=
  problem (x : ℝ)
    minimize x^2
    subject to
      nonneg : x ≥ 0

#printp p

reformulation epigraphForm : p := by
  epigraph t

#printp epigraphForm
#check epigraphForm.equivalence

example : p.IsGlobalOptimum ⟨0, le_rfl⟩ := by
  -- The epigraph point (0, 0) satisfies both constraints.
  let z : FeasiblePoint epigraphForm := ⟨(0, 0), by
    change 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ^ 2 ≤ 0
    norm_num⟩

  -- Every feasible point has objective t ≥ x² ≥ 0.
  have hz : epigraphForm.IsGlobalOptimum z := by
    intro y
    change (0 : ℝ) ≤ y.1.2
    exact le_trans (sq_nonneg y.1.1) y.2.2

  -- The certificate's backward map recovers x and transfers optimality.
  exact epigraphForm.equivalence.map_isGlobalOptimum_backward hz

-- Name the epigraph constraint.
reformulation labeledEpigraphForm : p := by
  epigraph t as objectiveBound

#printp labeledEpigraphForm
#check labeledEpigraphForm.equivalence

end Epigraph

namespace Parameterized
noncomputable section

def p (a : ℝ) :=
  problem (x : ℝ)
    minimize (x - a)^2
    subject to
      lower : x ≥ a

/-! Printing the family retains the parameter `a` symbolically. -/
#printp p

-- Reformulate a particular member of the problem family.
reformulation concreteEpigraph : (p 3) := by
  epigraph t

#printp concreteEpigraph
example : GlobalEquivalence (p 3) concreteEpigraph := concreteEpigraph.equivalence

section

variable (shift : ℝ)

-- A local argument produces a reformulation family with the same parameter.
reformulation shiftedEpigraph : (p shift) := by
  epigraph t

example : GlobalEquivalence (p shift) (shiftedEpigraph shift) :=
  shiftedEpigraph.equivalence shift

end

#printp shiftedEpigraph

end
end Parameterized

end Examples.GettingStarted.Basic
