/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Conic reformulations

`conic at label` performs an exact rewrite of a selected constraint; optional
`using` selects its rule.

Bare `conic` finishes the script by rewriting supported constraints as cone
memberships and certifying the complete problem as an affine cone program.
It records a concrete conic form and certificates alongside the final problem.
Objective bounds and coordinate substitutions remain explicit steps.
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
      nonnegative : 0 ≤ x ∧ 0 ≤ y
      balance : x + y = 1

reformulation conicProb : p := by
  conic

#printp conicProb
#check conicProb.conicForm.data
example : GlobalEquivalence p conicProb := conicProb.equivalence
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

-- Affine certification expands transparent def/abbrev helpers automatically.
reformulation conicProb : p := by
  conic

/-! Printed objectives and constraints keep their original helper references. -/
#printp conicProb
example : GlobalEquivalence p conicProb := conicProb.equivalence
example : IsConic conicProb := conicProb.isConic

end Helpers

namespace Polyhedral

def p :=
  problem (x : ℝ)
    minimize |x - 2|
    subject to
      magnitude : |x| ≤ 5
      nonnegative : 0 ≤ x

-- These selected rewrites expose linear bounds and record equivalence.
-- ANCHOR: linearBounds
reformulation linearBounds : p := by
  conic at magnitude
  epigraph t as distance
  conic at distance
-- ANCHOR_END: linearBounds

#printp linearBounds
example : GlobalEquivalence p linearBounds := linearBounds.equivalence

/-! Continue from the intermediate problem and compose the two equivalences. -/
-- ANCHOR: conicChain
reformulation conicProb : linearBounds := by
  conic

example : GlobalEquivalence p conicProb :=
  linearBounds.equivalence.trans conicProb.equivalence
-- ANCHOR_END: conicChain

#printp conicProb
example : conicProb.conicForm.data.toProblem = conicProb := conicProb.conicForm.represents
example : IsConic conicProb := conicProb.isConic

end Polyhedral

end
end Examples.GettingStarted.Conic
