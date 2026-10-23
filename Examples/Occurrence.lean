import Morew.Reformulation.Command

/-!
# Exposing nonlinear components with occurrence bounds

Named definitions are reusable expressions. Selecting one replaces its direct
use at the chosen location; the definition remains available elsewhere.
-/

namespace Morew.Examples.Occurrence

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

example : GlobalEquivalence regularized regularizedConic := regularizedConic.equivalence
example : IsConic regularizedConic := regularizedConic.isConic

def budgeted :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      budget : |x| + y ^ 2 ≤ 10

reformulation budgetedConic : budgeted := by
  epigraph a at (|x|) in budget as magnitude_bound
  epigraph b at (y ^ 2) in budget as square_bound
  conic

example : GlobalEquivalence budgeted budgetedConic := budgetedConic.equivalence
example : IsConic budgetedConic := budgetedConic.isConic

end
end Morew.Examples.Occurrence
