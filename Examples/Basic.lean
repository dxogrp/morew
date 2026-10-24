/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

open Morew
open Real

/-
Epigraph rewriting example
-/
namespace Examples.Basic

namespace Epigraph
noncomputable

def p :=
  problem (x : ℝ)
    minimize x^2
    subject to
      nonneg : x ≥ 0

#printp p

-- Default epigraph rewriting
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

-- Epigraph rewriting with explicit label
reformulation labeledEpigraphForm : p := by
  epigraph t as objectiveBound

#printp labeledEpigraphForm
#check labeledEpigraphForm.equivalence

end Epigraph

/-
Parameterized problem examples
-/
namespace Parameterized
noncomputable section

def p (a : ℝ) :=
  problem (x : ℝ)
    minimize (x - a)^2
    subject to
      lower : x ≥ a

-- Printing the family retains the parameter `a` symbolically.
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

/-
Substitute and epigraph rewriting example
-/
namespace LogSquared
noncomputable section

def p :=
  problem (x : ℝ)
    minimize (log x)^2
    subject to
      pos : x > 0

#printp p

reformulation exponentialEpigraph : p := by
  substitute x := exp u
  epigraph t

#printp exponentialEpigraph
example : GlobalEquivalence p exponentialEpigraph := exponentialEpigraph.equivalence

end
end LogSquared

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
