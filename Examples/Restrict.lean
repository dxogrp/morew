/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic

/-!
# Selecting feasible representatives

`restrict label : proposition using repair` can discard feasible points when
each has a representative satisfying the new condition with no worse objective.
The certificate preserves global optimization behavior; the feasible sets may differ.
-/

namespace Examples.Restrict

open Morew
noncomputable section

-- Sorting interchangeable variables chooses an ordered representative.
def symmetric :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      lower_x : 0 ≤ x
      lower_y : 0 ≤ y

def sortingRepair : GlobalImprovement symmetric
    (symmetric.addConstraint (fun point => point.1 ≤ point.2)) where
  map point := ⟨(min point.1.1 point.1.2, max point.1.1 point.1.2),
    ⟨⟨le_min point.2.1 point.2.2, point.2.1.trans (le_max_left _ _)⟩,
      min_le_max⟩⟩
  objective_le point := by
    change min point.1.1 point.1.2 + max point.1.1 point.1.2 ≤ point.1.1 + point.1.2
    rw [min_add_max]

reformulation ordered : symmetric := by
  restrict ordered : x ≤ y using sortingRepair

#printp ordered
example : GlobalEquivalence symmetric ordered := ordered.equivalence

-- Restrict to nonnegative points by replacing x with |x|.
def maximum :=
  problem (x : ℝ)
    maximize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

def absoluteRepair : GlobalImprovement maximum
    (maximum.addConstraint (fun x => 0 ≤ x)) where
  map point := ⟨|point.1|,
    ⟨⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (abs_nonneg _), abs_le.mpr point.2⟩,
      abs_nonneg _⟩⟩
  -- OrderDual makes objective_le require x ≤ |x| for this maximization problem.
  objective_le point := le_abs_self point.1

reformulation nonnegativeMaximum : maximum := by
  restrict nonnegative : 0 ≤ x using absoluteRepair

#printp nonnegativeMaximum
example : GlobalEquivalence maximum nonnegativeMaximum := nonnegativeMaximum.equivalence

-- Select a nonnegative representative after square substitution.
-- Substituting `x := u ^ 2` allows both signs of `u`.
-- `restrictionImprovement` reuses the square-root preimage in `squareCoverage`
-- to repair each `u` to `√(u²) = |u|`. Proving this preimage is nonnegative
-- justifies adding `0 ≤ u`; its square is unchanged, so the objective is preserved.
-- Both `u = ±2` initially minimize the problem; the restriction retains `u = 2`.
def nonnegativeSource :=
  problem (x : ℝ)
    minimize (x - 4) ^ 2
    subject to nonnegative : 0 ≤ x

def squareCoverage : FeasibleSurjection nonnegativeSource (fun u : ℝ => u ^ 2) where
  preimage point := Real.sqrt point.1
  rightInverse point := Real.sq_sqrt point.2

reformulation principalCoordinates : nonnegativeSource := by
  substitute x := u ^ 2
  restrict branch : 0 ≤ u using
    squareCoverage.restrictionImprovement (fun u => 0 ≤ u)
      (fun point => Real.sqrt_nonneg point.1)

#printp principalCoordinates
example : GlobalEquivalence nonnegativeSource principalCoordinates := principalCoordinates.equivalence
example (u : ℝ) (hu : principalCoordinates.feasible u) : Real.sqrt (u ^ 2) = u :=
  Real.sqrt_sq hu

end
end Examples.Restrict
