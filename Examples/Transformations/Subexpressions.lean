/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Epigraphs of subexpressions

Use `let` to name an expression shared by the objective and constraints.
An `epigraph` step can replace a selected subexpression by a new variable and
add its epigraph bound, provided the surrounding expression preserves the
required inequality. Its clauses identify the expression and evidence:
- `at` selects a direct `let` reference or a parenthesized expression;
  exactly one match is required.
- `in` selects a named constraint; without it, selection is within the objective.
- `as` names the added bound constraint.
- `using` supplies an explicit context certificate; otherwise Morew attempts
  automatic certification.

Introducing these bounds records equivalence. A final `conic` or `nlp` step
then certifies the complete reformulated problem in the chosen form.
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

def nonlinear :=
  problem (x y t : ℝ)
    minimize (x * y - 1) ^ 2 + t
    subject to
      error : |x ^ 2 - y| ≤ t
      budget : |x| + y ^ 2 ≤ 10

-- The error is already a direct bound. In the budget, first replace |x|
-- by a variable and add the direct bound named `magnitude`.
reformulation smoothConstraints : nonlinear := by
  nlp at error using Rewrite.absEpigraph
  epigraph a at (|x|) in budget as magnitude
  nlp at magnitude
  nlp

#printp smoothConstraints
example : GlobalEquivalence nonlinear smoothConstraints := smoothConstraints.equivalence
example : smoothConstraints.nlpForm.data.toProblem = smoothConstraints :=
  smoothConstraints.nlpForm.represents
example : IsSmoothNLP smoothConstraints := smoothConstraints.isSmoothNLP

end
end Examples.Transformations.Subexpressions
