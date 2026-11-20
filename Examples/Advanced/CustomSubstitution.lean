/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Basic

/-!
# Custom coordinate substitutions

In the following problem, the change of variables `x = u + c` preserves `c`
and changes the objective to `u²`.
-/

@[expose] public section

namespace Examples.Advanced.CustomSubstitution

open Morew
noncomputable section

def source :=
  problem (c x : ℝ)
    minimize (x - c) ^ 2
    subject to nonneg : 0 ≤ c

def shift (c u : ℝ) : ℝ := u + c

/-!
## Coordinate parameterization

A `CoordinateParameterization` specifies a range of source values and a
preimage for every value in that range. Its `rightInverse` field proves that
applying the substitution to the chosen preimage recovers the source value.
Here every real value has the preimage `x - c`, so the range is `True`.
The argument `c : R → ℝ` allows the offset to depend on retained coordinates.
-/

def shiftRule {R : Type*} (c : R → ℝ) :
    CoordinateParameterization (fun r u => shift (c r) u) where
  range _ _ := True
  preimage r x := x.1 - c r
  rightInverse _ _ := sub_add_cancel _ _

/-! `via` selects this parameterization without registering it. -/
reformulation selected : source := by
  substitute x := shift c u via shiftRule

#printp selected

example : GlobalEquiv source selected := selected.equiv

example (c u : ℝ) : selected.objective (c, u) = u ^ 2 := by
  change (u + c - c) ^ 2 = u ^ 2
  rw [add_sub_cancel_right]

example (c u : ℝ) : selected.feasible (c, u) ↔ 0 ≤ c := Iff.rfl

/-! The recovery map sends `(c, u)` to `(c, u + c)`. -/
example (point : FeasiblePoint selected) :
    (selected.equiv.backward.map point).val =
      (point.val.1, point.val.2 + point.val.1) := rfl

/-!
## A complete substitution certificate

`CoordinateParameterization.toFeasibleSurjection` combines the rule with proof
that every feasible source point has its selected coordinate in the range.
The two identity equivalences identify the retained coordinate `c` and the
selected coordinate in each decision space. Coverage is immediate here because
the range is `True`; the constraint `0 ≤ c` remains in the target problem.
-/

def coverage :
    FeasibleSurjection source (fun p : ℝ × ℝ => (p.1, shift p.1 p.2)) :=
  (shiftRule (fun c : ℝ => c)).toFeasibleSurjection source
    (Equiv.refl _) (Equiv.refl _) (fun _ _ => True.intro)

/-! `using` supplies this certificate for the complete current problem. -/
reformulation supplied : source := by
  substitute x := shift c u using coverage

example : supplied = selected := rfl

/-!
## Registration

The attribute `[morew_substitute]` registers a parameterization for automatic
selection. A local registration applies only within its section.
-/

section

attribute [local morew_substitute] shiftRule

reformulation automatic : source := by
  substitute x := shift c u

example : automatic = selected := rfl

end

/-!
A scoped registration is activated by `open scoped` in the section where the
rule is needed.
-/

namespace Scoped

attribute [scoped morew_substitute] shiftRule

end Scoped

section

open scoped Scoped

reformulation scopedSelection : source := by
  substitute x := shift c u

example : scopedSelection = selected := rfl

end

end
end Examples.Advanced.CustomSubstitution
