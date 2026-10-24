import Morew.Reformulation.Command

/-!
# Lifting objective and constraint components

We can use `let` to name a reusable expression available in the objective and constraints.
The following commands after `epigraph` allow us to lift individual objective and constraint components:
- `at` selects a direct `let` reference or a parenthesized expression;
  exactly one match is required.
- `in` selects a named constraint; without it, selection is within the objective.
- `as` names the added bound constraint.
- `using` supplies an explicit context certificate; otherwise Morew attempts
  automatic certification.
-/

namespace Morew.Examples.Components

open Morew
noncomputable section

def regularized :=
  problem (x : ℝ)
    let loss := (x - 1) ^ 2
    let penalty := |x|
    minimize loss + penalty

reformulation regularizedConic : regularized := by
  epigraph a at loss as loss_bound
  epigraph b at penalty as penalty_bound
  conic

#printp regularizedConic
example : GlobalEquivalence regularized regularizedConic := regularizedConic.equivalence
example : IsConic regularizedConic := regularizedConic.isConic

def budgeted :=
  problem (x y : ℝ)
    let abs_y := |y|
    minimize x ^ 2 + y
    subject to
      budget : |x| + y ^ 2 ≤ 10
      bound : abs_y ≤ 5

reformulation budgetedConic : budgeted := by
  epigraph a at (x ^ 2) as epi_sq_x
  epigraph b at (|x|) in budget as magnitude_bound
  epigraph c at (y ^ 2) in budget as square_bound
  epigraph d at abs_y in bound as abs_bound
  conic

#printp budgetedConic
example : GlobalEquivalence budgeted budgetedConic := budgetedConic.equivalence
example : IsConic budgetedConic := budgetedConic.isConic

end
end Morew.Examples.Components
