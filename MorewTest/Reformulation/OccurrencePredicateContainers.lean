import Morew.Reformulation.Command

/-!
# Predicate operands inside computational containers

Occurrence counting follows direct references through containers and their
projections without reducing them. Type, proof, and instance operands remain
excluded even when another operand contains a selectable predicate.
-/

namespace MorewTest.Reformulation.OccurrencePredicateContainers

open Morew
noncomputable section

def repeatedNamed :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to cap : (loss ≤ 1, True).1 ∧ loss ≤ 2

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedNamedLift : repeatedNamed := by
  epigraph t at loss in cap

def repeatedExpression :=
  problem (x : ℝ)
    minimize x
    subject to cap : (x ^ 2 ≤ 1, True).1 ∧ x ^ 2 ≤ 2

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedExpressionLift : repeatedExpression := by
  epigraph t at (x ^ 2) in cap

def singleNamed :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to cap : (loss ≤ 1, True).1

theorem upperContext : ConstraintBoundContext (fun _ : ℝ => True)
    (fun x => x ^ 2 ≤ 1) (fun x => x ^ 2) (fun _ t => t ≤ 1) .upper where
  atValue _ := Iff.rfl
  backward _ _ _ bound target := bound.trans target

reformulation singleNamedLift : singleNamed := by
  epigraph t at loss in cap using upperContext

example : GlobalEquivalence singleNamed singleNamedLift := singleNamedLift.equivalence
example (x t : ℝ) : singleNamedLift.objective (x, t) = x := rfl
example (x t : ℝ) : singleNamedLift.feasible (x, t) ↔ t ≤ 1 ∧ x ^ 2 ≤ t := Iff.rfl

def singleExpression :=
  problem (x : ℝ)
    minimize x
    subject to cap : (x ^ 2 ≤ 1, True).1

reformulation singleExpressionLift : singleExpression := by
  epigraph t at (x ^ 2) in cap using upperContext

example : GlobalEquivalence singleExpression singleExpressionLift :=
  singleExpressionLift.equivalence
example (x t : ℝ) : singleExpressionLift.feasible (x, t) ↔
    t ≤ 1 ∧ x ^ 2 ≤ t := Iff.rfl

def letContainer :=
  problem (x : ℝ)
    minimize x
    subject to cap : let predicates := (True, x ^ 2 ≤ 1); predicates.2

reformulation letContainerLift : letContainer := by
  epigraph t at (x ^ 2) in cap using upperContext

example : GlobalEquivalence letContainer letContainerLift := letContainerLift.equivalence
example (x t : ℝ) : letContainerLift.feasible (x, t) ↔ t ≤ 1 ∧ x ^ 2 ≤ t := Iff.rfl

-- Both tuple fields are direct occurrences even though the projection uses
-- only the first. Reducing the let or projection before counting is incorrect.
def repeatedLet :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to cap : let predicates := (loss ≤ 1, loss ≤ 2); predicates.1

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedLetLift : repeatedLet := by
  epigraph t at loss in cap

def optionContainer :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to cap : (some (loss ≤ 1)).getD True

reformulation optionContainerLift : optionContainer := by
  epigraph t at loss in cap using upperContext

example : GlobalEquivalence optionContainer optionContainerLift := optionContainerLift.equivalence
example (x t : ℝ) : optionContainerLift.feasible (x, t) ↔
    t ≤ 1 ∧ x ^ 2 ≤ t := Iff.rfl

private def acceptsProof {P : Prop} (_ : P) : Prop := True
private def indexedPredicate (P : Prop) (_ : P) : Prop := True

-- References inside the implicit proof type, the proof term, and an explicit
-- proposition indexing a later proof must not make the selector ambiguous.
def proofOperands :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to cap :
      acceptsProof (le_refl loss) ∧
        indexedPredicate (loss ≤ loss) (le_refl loss) ∧ (loss ≤ 1, True).1

reformulation proofOperandsLift : proofOperands := by
  epigraph t at loss in cap

example (x t : ℝ) : proofOperandsLift.feasible (x, t) ↔
    (True ∧ True ∧ t ≤ 1) ∧ x ^ 2 ≤ t := Iff.rfl

def typeOperand :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to cap : Nonempty { y : ℝ // y ≤ loss } ∧ (loss ≤ 1, True).1

reformulation typeOperandLift : typeOperand := by
  epigraph t at loss in cap

example (x t : ℝ) : typeOperandLift.feasible (x, t) ↔
    (Nonempty { y : ℝ // y ≤ x ^ 2 } ∧ t ≤ 1) ∧ x ^ 2 ≤ t := Iff.rfl

@[instance_reducible]
private def shiftedOrder (offset : ℝ) : LE ℝ := ⟨fun a b => a + offset ≤ b⟩
private def acceptsOrder (_ : LE ℝ) : Prop := True

-- Class-valued operands remain instance evidence even when supplied to an
-- explicit parameter or retained in a local let.
def instanceOperands :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to cap :
      (let order := shiftedOrder loss; acceptsOrder order) ∧
        acceptsOrder (shiftedOrder loss) ∧ (loss ≤ 1, True).1

reformulation instanceOperandsLift : instanceOperands := by
  epigraph t at loss in cap

example (x t : ℝ) : instanceOperandsLift.feasible (x, t) ↔
    (True ∧ True ∧ t ≤ 1) ∧ x ^ 2 ≤ t := Iff.rfl

private def hiddenPair (x : ℝ) : Prop × Prop := (x ^ 2 ≤ 1, True)

def hidden := problem (x : ℝ) minimize x subject to cap : (hiddenPair x).1

/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation hiddenLift : hidden := by
  epigraph t at (x ^ 2) in cap using upperContext

end
end MorewTest.Reformulation.OccurrencePredicateContainers
