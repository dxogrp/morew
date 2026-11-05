/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Epigraphs of subexpressions

Use `let` to name an expression shared by the objective and constraints.
An `epigraph` step replaces a selected subexpression by a new variable and
adds its epigraph bound, with a monotonicity certificate for the surrounding
objective or constraint.

- `at` selects a `let` reference or a parenthesized expression with one occurrence.
- `in` selects a constraint; by default, selection is within the objective.
- `as` names the added bound.
- `using` supplies a context certificate; otherwise Morew attempts to infer it.
-/

namespace Examples.Transformations.Subexpressions

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
example : GlobalEquiv regularized regularizedConic := regularizedConic.equiv
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
example : GlobalEquiv budgeted budgetedConic := budgetedConic.equiv
example : IsConic budgetedConic := budgetedConic.isConic

def nonlinear :=
  problem (x y t : ℝ)
    minimize (x * y - 1) ^ 2 + t
    subject to
      error : |x ^ 2 - y| ≤ t
      budget : |x| + y ^ 2 ≤ 10

-- Introduce a direct bound on `|x|` before rewriting the budget constraint.
reformulation smoothConstraints : nonlinear := by
  nlp at error using Rewrite.absEpigraph
  epigraph a at (|x|) in budget as magnitude
  nlp at magnitude
  nlp

#printp smoothConstraints
example : GlobalEquiv nonlinear smoothConstraints := smoothConstraints.equiv
example : smoothConstraints.nlpForm.data.toProblem = smoothConstraints :=
  smoothConstraints.nlpForm.represents
example : IsSmoothNLP smoothConstraints := smoothConstraints.isSmoothNLP

end
end Examples.Transformations.Subexpressions
