/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Command

/-!
# Selected objective and constraint bound lifts

These examples check the generated semantics, preserved local bindings and row
order, explicit context evidence, and composition with conic conversion.
-/

namespace MorewTest.Reformulation.OccurrenceBounds

open Morew
noncomputable section

def compound :=
  problem (x : ℝ)
    minimize x ^ 2 + |x|

reformulation split : compound := by
  epigraph a at (x ^ 2)
  epigraph b at (|x|) as magnitude

example : GlobalEquivalence compound split := split.equivalence
example (x a b : ℝ) : split.objective ((x, a), b) = a + b := rfl
example (x a b : ℝ) : split.feasible ((x, a), b) ↔ x ^ 2 ≤ a ∧ |x| ≤ b := Iff.rfl

/--
info: problem (x a b : ℝ)
  minimize a + b
  subject to
    epigraph_a : x ^ 2 ≤ a
    magnitude : |x| ≤ b
-/
#guard_msgs in
#printp split

reformulation converted : compound := by
  epigraph a at (x ^ 2)
  epigraph b at (|x|)
  conic

example : GlobalEquivalence compound converted := converted.equivalence
example : Conic.Form converted := converted.conicForm
example : IsConic converted := converted.isConic
example : converted.conicForm.data.rowCount = 3 := rfl

reformulation targetedConverted : compound := by
  epigraph a at (x ^ 2) as square_bound
  conic at square_bound
  epigraph b at (abs x) as magnitude_bound
  conic at magnitude_bound
  conic

example : GlobalEquivalence compound targetedConverted := targetedConverted.equivalence
example : IsConic targetedConverted := targetedConverted.isConic
example : targetedConverted.conicForm.data.rowCount = 3 := rfl

def nestedExponential := problem (x : ℝ) minimize Real.exp (x ^ 2 + 1) + x

reformulation nestedExponentialSplit : nestedExponential := by
  epigraph t at (x ^ 2)

example : GlobalEquivalence nestedExponential nestedExponentialSplit :=
  nestedExponentialSplit.equivalence
example (x t : ℝ) : nestedExponentialSplit.objective (x, t) = Real.exp (t + 1) + x := rfl
example (x t : ℝ) : nestedExponentialSplit.feasible (x, t) ↔ x ^ 2 ≤ t := Iff.rfl

-- Compiled declarations may extract the real numeral's AtLeastTwo evidence
-- into an auxiliary theorem; typed selection must respect proof irrelevance.
def numeralExpression := problem (x : ℝ) minimize (x + 2) ^ 2 + |x|

reformulation numeralExpressionSplit : numeralExpression := by
  epigraph t at ((x + 2) ^ 2)

example : GlobalEquivalence numeralExpression numeralExpressionSplit :=
  numeralExpressionSplit.equivalence
example (x t : ℝ) : numeralExpressionSplit.objective (x, t) = t + |x| := rfl
example (x t : ℝ) : numeralExpressionSplit.feasible (x, t) ↔
    (x + 2) ^ 2 ≤ t := Iff.rfl

def named :=
  problem (x : ℝ)
    let loss : ℝ := (x - 1) ^ 2
    let penalty := |x|
    let unused := loss + penalty
    minimize loss + penalty
    subject to
      cap : loss ≤ 10

reformulation namedSplit : named := by
  epigraph t at loss as loss_bound

example : GlobalEquivalence named namedSplit := namedSplit.equivalence
example (x t : ℝ) : namedSplit.objective (x, t) = t + |x| := rfl
example (x t : ℝ) : namedSplit.feasible (x, t) ↔
    (x - 1) ^ 2 ≤ 10 ∧ (x - 1) ^ 2 ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  let loss : ℝ := (x - 1) ^ 2
  let penalty := |x|
  let unused := loss + penalty
  minimize t + penalty
  subject to
    cap : loss ≤ 10
    loss_bound : loss ≤ t
-/
#guard_msgs in
#printp namedSplit

reformulation continued : namedSplit := by
  epigraph b at penalty
  conic

example : GlobalEquivalence namedSplit continued := continued.equivalence
example : IsConic continued := continued.isConic

def equalDefinitions :=
  problem (x : ℝ)
    let first := x ^ 2
    let second := x ^ 2
    minimize first + second

reformulation oneDefinition : equalDefinitions := by
  epigraph t at first

/--
info: problem (x t : ℝ)
  let first := x ^ 2
  let second := x ^ 2
  minimize t + second
  subject to
    epigraph_t : first ≤ t
-/
#guard_msgs in
#printp oneDefinition

def namedConstraints :=
  problem (x y : ℝ)
    let loss := |x|
    minimize loss + y
    subject to
      before : 0 ≤ x
      budget : loss + y ^ 2 ≤ 10
      after : y ≤ 3

reformulation constraintSplit : namedConstraints := by
  epigraph a at loss in budget as abs_bound

example : GlobalEquivalence namedConstraints constraintSplit := constraintSplit.equivalence
example (x y a : ℝ) : constraintSplit.objective ((x, y), a) = |x| + y := rfl
example (x y a : ℝ) : constraintSplit.feasible ((x, y), a) ↔
    0 ≤ x ∧ a + y ^ 2 ≤ 10 ∧ y ≤ 3 ∧ |x| ≤ a := Iff.rfl

/--
info: problem (x y a : ℝ)
  let loss := |x|
  minimize loss + y
  subject to
    before : 0 ≤ x
    budget : a + y ^ 2 ≤ 10
    after : y ≤ 3
    abs_bound : loss ≤ a
-/
#guard_msgs in
#printp constraintSplit

def budgeted :=
  problem (x y : ℝ)
    let abs_y := |y|
    minimize x ^ 2 + y
    subject to
      budget : |x| + y ^ 2 ≤ 10
      bound : abs_y ≤ 5

-- Keep this chain within Lean's default heartbeat budget. Re-elaborating each
-- complete occurrence certificate used to exhaust that budget for this chain.
reformulation budgetedConic : budgeted := by
  epigraph a at (x ^ 2) as epi_sq_x
  epigraph b at (|x|) in budget as magnitude_bound
  epigraph c at (y ^ 2) in budget as square_bound
  epigraph d at abs_y in bound as abs_bound
  conic

example : GlobalEquivalence budgeted budgetedConic := budgetedConic.equivalence
example : Conic.Form budgetedConic := budgetedConic.conicForm
example : IsConic budgetedConic := budgetedConic.isConic
example : budgetedConic.conicForm.data.rowCount = 8 := rfl
example (x y a b c d : ℝ) :
    budgetedConic.objective (((((x, y), a), b), c), d) = a + y := rfl

/--
info: problem (x y a b c d : ℝ)
  let abs_y := |y|
  minimize a + y
  subject to
    budget : 10 - (b + c) ∈ ℝ₊
    bound : 5 - d ∈ ℝ₊
    epi_sq_x_conic_1 : (a, 1 / 2, ![x]) ∈ RSOC 1
    magnitude_bound_conic_1 : b - x ∈ ℝ₊
    magnitude_bound_conic_2 : b - -x ∈ ℝ₊
    square_bound_conic_1 : (c, 1 / 2, ![y]) ∈ RSOC 1
    abs_bound_conic_1 : d - y ∈ ℝ₊
    abs_bound_conic_2 : d - -y ∈ ℝ₊
-/
#guard_msgs in
#printp budgetedConic

def maximum :=
  problem (x : ℝ)
    let score := min x (2 * x)
    maximize score + x
    subject to
      budget : |x| + x ≤ 10

reformulation maximumSplit : maximum := by
  hypograph t at score
  epigraph a at (|x|) in budget

example : GlobalEquivalence maximum maximumSplit := maximumSplit.equivalence
example (x t a : ℝ) : maximumSplit.objective ((x, t), a) = t + x := rfl
example (x t a : ℝ) : maximumSplit.feasible ((x, t), a) ↔
    a + x ≤ 10 ∧ t ≤ min x (2 * x) ∧ |x| ≤ a := Iff.rfl

/--
info: problem (x t a : ℝ)
  let score := min x (2 * x)
  maximize t + x
  subject to
    budget : a + x ≤ 10
    hypograph_t : t ≤ score
    epigraph_a : |x| ≤ a
-/
#guard_msgs in
#printp maximumSplit

theorem maximumContext : ObjectiveHypographContext maximum
    (fun x => min x (2 * x)) (fun x t => t + x) where
  atValue _ := rfl
  backward _ _ _ bound := add_le_add bound le_rfl

reformulation maximumUsing : maximum := by
  hypograph t at score using maximumContext

reformulation maximumLabeledUsing : maximum := by
  hypograph t at score as score_bound using maximumContext

example : GlobalEquivalence maximum maximumUsing := maximumUsing.equivalence
example : GlobalEquivalence maximum maximumLabeledUsing := maximumLabeledUsing.equivalence
example : maximumUsing = maximumLabeledUsing := rfl
example (x t : ℝ) : maximumLabeledUsing.feasible (x, t) ↔
    |x| + x ≤ 10 ∧ t ≤ min x (2 * x) := Iff.rfl

reformulation maximumConverted : maximum := by
  hypograph t at score as score_bound
  conic at score_bound
  epigraph a at (abs x) in budget as magnitude_bound
  conic at magnitude_bound
  conic

example : GlobalEquivalence maximum maximumConverted := maximumConverted.equivalence
example : IsConic maximumConverted := maximumConverted.isConic
example : maximumConverted.conicForm.data.sense = .maximize := rfl
example : maximumConverted.conicForm.data.rowCount = 5 := rfl

def lowerMinimum :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : 1 ≤ x ^ 2

reformulation lowerMinimumSplit : lowerMinimum := by
  hypograph t at (x ^ 2) in lower

example : GlobalEquivalence lowerMinimum lowerMinimumSplit := lowerMinimumSplit.equivalence
example (x t : ℝ) : lowerMinimumSplit.feasible (x, t) ↔
    1 ≤ t ∧ t ≤ x ^ 2 := Iff.rfl

def lowerMaximum :=
  problem (x : ℝ)
    maximize x
    subject to
      lower : 1 ≤ x ^ 2

reformulation lowerMaximumSplit : lowerMaximum := by
  hypograph t at (x ^ 2) in lower as lower_bound

example : GlobalEquivalence lowerMaximum lowerMaximumSplit := lowerMaximumSplit.equivalence

def grouped :=
  problem (x : ℝ)
    minimize x
    subject to
      bounds : (|x| + x ≤ 10 ∧ x ≠ 0) ∧ True

reformulation groupedSplit : grouped := by
  epigraph t at (|x|) in bounds

example (x t : ℝ) : groupedSplit.feasible (x, t) ↔
    ((t + x ≤ 10 ∧ x ≠ 0) ∧ True) ∧ |x| ≤ t := Iff.rfl

def weighted :=
  problem (weight x : ℝ)
    let loss := x ^ 2
    minimize weight * loss
    subject to
      nonnegative : 0 ≤ weight

theorem weightedContext : ObjectiveEpigraphContext weighted
    (fun p => p.2 ^ 2) (fun p t => p.1 * t) where
  atValue _ := rfl
  backward _ feasible _ bound := mul_le_mul_of_nonneg_left bound feasible

reformulation weightedSplit : weighted := by
  epigraph t at loss as loss_bound using weightedContext

example : GlobalEquivalence weighted weightedSplit := weightedSplit.equivalence

def weightedConstraint :=
  problem (weight x : ℝ)
    minimize x
    subject to
      nonnegative : 0 ≤ weight
      budget : weight * |x| ≤ 10

theorem weightedConstraintContext : ConstraintBoundContext
    (fun p : ℝ × ℝ => 0 ≤ p.1) (fun p => p.1 * |p.2| ≤ 10)
    (fun p => |p.2|) (fun p t => p.1 * t ≤ 10) .upper where
  atValue _ := Iff.rfl
  backward _ retained _ bound target :=
    (mul_le_mul_of_nonneg_left bound retained).trans target

reformulation weightedConstraintSplit : weightedConstraint := by
  epigraph t at (|x|) in budget as abs_bound using weightedConstraintContext

example : GlobalEquivalence weightedConstraint weightedConstraintSplit :=
  weightedConstraintSplit.equivalence

def sharedNames :=
  problem (x : ℝ)
    let loss := |x|
    minimize x
    subject to
      loss : loss ≤ 10

reformulation sharedNamesSplit : sharedNames := by
  epigraph t at (loss) in loss as t

example (x t : ℝ) : sharedNamesSplit.feasible (x, t) ↔ t ≤ 10 ∧ |x| ≤ t := Iff.rfl

def logarithmic :=
  problem (x : ℝ)
    let loss := (Real.log x) ^ 2
    let penalty := x
    minimize loss + penalty
    subject to
      positive : 0 < x

reformulation logarithmicSplit : logarithmic := by
  substitute x := Real.exp u
  epigraph t at loss

example : GlobalEquivalence logarithmic logarithmicSplit := logarithmicSplit.equivalence
example (u t : ℝ) : logarithmicSplit.objective (u, t) = t + Real.exp u := rfl
example (u t : ℝ) : logarithmicSplit.feasible (u, t) ↔ u ^ 2 ≤ t := Iff.rfl

def natural := problem (x : ℕ) minimize x + 1

theorem naturalContext : ObjectiveEpigraphContext natural (fun x => x) (fun _ t => t + 1) where
  atValue _ := rfl
  backward _ _ _ bound := Nat.add_le_add_right bound 1

reformulation naturalSplit : natural := by
  epigraph t at (x) using naturalContext

example : GlobalEquivalence natural naturalSplit := naturalSplit.equivalence
example (x t : ℕ) : naturalSplit.objective (x, t) = t + 1 := rfl

end
end MorewTest.Reformulation.OccurrenceBounds
