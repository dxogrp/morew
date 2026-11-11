/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Conic reformulations

`conic at label` rewrites a selected constraint; `using` selects a rule explicitly.
Bare `conic` rewrites supported constraints and certifies an affine cone program,
recording its conic form and equivalence certificate. Introduce objective bounds
and coordinate substitutions as separate steps.
-/

namespace Examples.GettingStarted.Conic

open Morew
open Real
noncomputable section

namespace Linear

def p :=
  problem (x y : ℝ)
    minimize x + 2 * y
    subject to
      nonneg : 0 ≤ x ∧ 0 ≤ y
      balance : x + y = 1

reformulation conicProb : p := by
  conic

#printp conicProb
#check conicProb.conicForm.data
example : GlobalEquiv p conicProb := conicProb.equiv
example : conicProb.conicForm.data.toProblem = conicProb := conicProb.conicForm.represents
example : IsConic conicProb := conicProb.isConic

end Linear

namespace Helpers

def cost (x : ℝ) : ℝ := 2 * x + 1

def residual (x : ℝ) : ℝ := 3 * x - 4

def p :=
  problem (x : ℝ)
    minimize cost x
    subject to
      budget : residual x ≤ 0

-- Affine certification expands transparent `def`/`abbrev` helpers automatically.
reformulation conicProb : p := by
  conic

/-! Printed objectives and constraints keep their original helper references. -/
#printp conicProb
example : GlobalEquiv p conicProb := conicProb.equiv
example : IsConic conicProb := conicProb.isConic

end Helpers

namespace Polyhedral

def p :=
  problem (x : ℝ)
    minimize |x - 2|
    subject to
      magnitude : |x| ≤ 5
      nonneg : 0 ≤ x

-- Rewrite the absolute-value bounds as linear inequalities.
-- ANCHOR: linearBounds
reformulation linearBounds : p := by
  conic at magnitude
  epigraph t as distance
  conic at distance
-- ANCHOR_END: linearBounds

#printp linearBounds
example : GlobalEquiv p linearBounds := linearBounds.equiv

/-! Continue from the intermediate problem and compose the two equivalences. -/
-- ANCHOR: conicChain
reformulation conicProb : linearBounds := by
  conic

example : GlobalEquiv p conicProb :=
  linearBounds.equiv.trans conicProb.equiv
-- ANCHOR_END: conicChain

#printp conicProb
example : conicProb.conicForm.data.toProblem = conicProb := conicProb.conicForm.represents
example : IsConic conicProb := conicProb.isConic

end Polyhedral

end
end Examples.GettingStarted.Conic
