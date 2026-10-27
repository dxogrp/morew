/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-!
# Certified complete conic reformulations

`conic at label` performs an exact rewrite of a selected constraint; optional
`using` selects its rule.

Bare `conic` finishes the script by rewriting supported constraints as cone
memberships and certifying the complete problem as an affine cone program.
It records a concrete conic form and certificates alongside the final problem.
Objective bounds and coordinate substitutions remain explicit steps.
-/

namespace Examples.Conic

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
-- The defaults allow 32 nested expansions, 1024 unfoldings, and 100000
-- cumulative expression nodes per source expression. Set any limit to zero
-- to disable expansion. `set_option … in` changes only the following command;
-- this example raises the depth, though these shallow helpers need no override.
set_option morew.affine.maxExpansionDepth 64 in
reformulation conicProb : p := by
  conic

-- Printed objectives and constraints keep their original helper references.
#printp conicProb
example : GlobalEquivalence p conicProb := conicProb.equivalence
example : IsConic conicProb := conicProb.isConic

end Helpers

namespace LogSquared

def p :=
  problem (x : ℝ)
    minimize (log x) ^ 2
    subject to
      positive : 0 < x

reformulation conicProb : p := by
  substitute x := exp u
  epigraph t
  conic

#printp conicProb
example : GlobalEquivalence p conicProb := conicProb.equivalence
example : IsConic conicProb := conicProb.isConic

end LogSquared

namespace Softplus

def p :=
  problem (x : ℝ)
    minimize Fn.softplus x
    subject to
      lower : -2 ≤ x

-- Terminal validation introduces the
-- finite auxiliary vector belonging to the softplus representation.
reformulation conicProb : p := by
  epigraph t as loss
  conic

#printp conicProb
#check conicProb.conicForm.data
example : GlobalEquivalence p conicProb := conicProb.equivalence

end Softplus
end
end Examples.Conic
