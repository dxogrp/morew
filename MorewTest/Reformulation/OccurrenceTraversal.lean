import Morew.Reformulation.Command

/-!
# Occurrences inside predicate operands and computational application heads

Selection visits logical operands independently of the bounded automatic
certifier. It still excludes type, proof, and instance arguments and does not
unfold external helper definitions.
-/

namespace MorewTest.Reformulation.OccurrenceTraversal

open Morew
noncomputable section

def disjunction :=
  problem (x : ℝ)
    let loss := x ^ 2
    minimize x
    subject to
      cap : loss ≤ 1 ∨ x ≤ 0

theorem disjunctionContext : ConstraintBoundContext (fun _ : ℝ => True)
    (fun x => x ^ 2 ≤ 1 ∨ x ≤ 0) (fun x => x ^ 2)
    (fun x t => t ≤ 1 ∨ x ≤ 0) .upper where
  atValue _ := Iff.rfl
  backward _ _ _ bound target :=
    target.elim (fun h => Or.inl (bound.trans h)) Or.inr

reformulation disjunctionSplit : disjunction := by
  epigraph t at loss in cap as loss_bound using disjunctionContext

example : GlobalEquivalence disjunction disjunctionSplit := disjunctionSplit.equivalence
example (x t : ℝ) : disjunctionSplit.objective (x, t) = x := rfl
example (x t : ℝ) : disjunctionSplit.feasible (x, t) ↔
    (t ≤ 1 ∨ x ≤ 0) ∧ x ^ 2 ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  let loss := x ^ 2
  minimize x
  subject to
    cap : t ≤ 1 ∨ x ≤ 0
    loss_bound : loss ≤ t
-/
#guard_msgs in
#printp disjunctionSplit

-- Finding an occurrence does not extend automatic predicate certification.
/-- error: cannot certify bound context -/
#guard_msgs (substring := true) in
reformulation disjunctionAutomatic : disjunction := by
  epigraph t at loss in cap

def existential :=
  problem (x : ℝ)
    minimize x
    subject to
      cap : ∃ y : ℝ, x ^ 2 ≤ y ∧ y ≤ 1

theorem existentialContext : ConstraintBoundContext (fun _ : ℝ => True)
    (fun x => ∃ y : ℝ, x ^ 2 ≤ y ∧ y ≤ 1) (fun x => x ^ 2)
    (fun _ t => ∃ y : ℝ, t ≤ y ∧ y ≤ 1) .upper where
  atValue _ := Iff.rfl
  backward _ _ _ bound target := by
    obtain ⟨y, lower, upper⟩ := target
    exact ⟨y, bound.trans lower, upper⟩

reformulation existentialSplit : existential := by
  epigraph t at (x ^ 2) in cap using existentialContext

example : GlobalEquivalence existential existentialSplit := existentialSplit.equivalence
example (x t : ℝ) : existentialSplit.feasible (x, t) ↔
    (∃ y : ℝ, t ≤ y ∧ y ≤ 1) ∧ x ^ 2 ≤ t := Iff.rfl

def repeated :=
  problem (x : ℝ)
    minimize x
    subject to cap : x ^ 2 ≤ 1 ∨ x ^ 2 ≤ 0

/-- error: ambiguous occurrence selector: found 2 occurrences in the selected location -/
#guard_msgs in
reformulation repeatedSplit : repeated := by
  epigraph t at (x ^ 2) in cap

def headLet :=
  problem (x : ℝ)
    minimize (let y := x ^ 2; fun z : ℝ => y + z) 1

theorem headLetContext : ObjectiveEpigraphContext headLet
    (fun x => x ^ 2) (fun _ t => t + 1) where
  atValue _ := rfl
  backward _ _ _ bound := add_le_add bound (le_refl 1)

reformulation headLetSplit : headLet := by
  epigraph t at (x ^ 2) using headLetContext

reformulation headLetAutomatic : headLet := by
  epigraph t at (x ^ 2)

example : GlobalEquivalence headLet headLetSplit := headLetSplit.equivalence
example : headLetAutomatic = headLetSplit := rfl
example (x t : ℝ) : headLetSplit.objective (x, t) = t + 1 := rfl
example (x t : ℝ) : headLetSplit.feasible (x, t) ↔ x ^ 2 ≤ t := Iff.rfl

-- Predicate mode survives the application head, its let initializer, and the
-- predicate's lambda binder. None of these reduces the selected expression.
def predicateHeadLet :=
  problem (x : ℝ)
    minimize x
    subject to
      cap : (let acceptable := fun z : ℝ => x ^ 2 ≤ z ∨ x ≤ 0; acceptable) 1

reformulation predicateHeadLetSplit : predicateHeadLet := by
  epigraph t at (x ^ 2) in cap using disjunctionContext

example : GlobalEquivalence predicateHeadLet predicateHeadLetSplit :=
  predicateHeadLetSplit.equivalence
example (x t : ℝ) : predicateHeadLetSplit.feasible (x, t) ↔
    (t ≤ 1 ∨ x ≤ 0) ∧ x ^ 2 ≤ t := Iff.rfl

private def hiddenPredicate (x : ℝ) : Prop := x ^ 2 ≤ 1 ∨ x ≤ 0

def hidden := problem (x : ℝ) minimize x subject to cap : hiddenPredicate x

/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation hiddenSplit : hidden := by
  epigraph t at (x ^ 2) in cap using disjunctionContext

def typeArgument :=
  problem (n : ℕ) minimize n subject to cap : Nonempty (Fin (n + 1))

/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation typeArgumentSplit : typeArgument := by
  epigraph t at (n + 1) in cap

private def acceptsProof {P : Prop} (_ : P) : Prop := True

def proofArgument :=
  problem (x : ℝ) minimize x subject to cap : acceptsProof (sq_nonneg x)

-- The implicit proposition indexes a proof argument, so it remains a type
-- parameter rather than a logical operand of the selected predicate.
/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation proofArgumentSplit : proofArgument := by
  epigraph t at (x ^ 2) in cap

private def acceptsOrder (_ : LE ℝ) : Prop := True

def instanceArgument :=
  problem (x : ℝ)
    minimize x
    subject to cap : acceptsOrder ⟨fun a b => a + x ^ 2 ≤ b⟩

/-- error: selector has no direct occurrence in the selected location -/
#guard_msgs in
reformulation instanceArgumentSplit : instanceArgument := by
  epigraph t at (x ^ 2) in cap

end
end MorewTest.Reformulation.OccurrenceTraversal
