/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Substitution through model-local definitions

Definition values and annotations follow renamed decisions, while replacement
inference distinguishes existing aliases from the one new decision variable.
-/

namespace MorewTest.Reformulation.LocalDefinitionSubstitution

open Morew
noncomputable section

def source :=
  problem (x : ℝ)
    let loss : ℝ := Real.log x
    let twice := loss + loss
    minimize twice
    subject to
      positive : 0 < x
      cap : loss ≤ 5

reformulation transformed : source := by
  substitute x := Real.exp u

example : GlobalEquivalence source transformed := transformed.equivalence
example (u : ℝ) : transformed.objective u = u + u := rfl
example (u : ℝ) : transformed.feasible u ↔ u ≤ 5 := Iff.rfl

/--
info: problem (u : ℝ)
  let loss : ℝ := u
  let twice := loss + loss
  minimize twice
  subject to
    cap : loss ≤ 5
-/
#guard_msgs in
#printp transformed

reformulation boundedFirst : source := by
  epigraph t
  substitute x := Real.exp u

example : GlobalEquivalence source boundedFirst := boundedFirst.equivalence
example (u t : ℝ) : boundedFirst.feasible (u, t) ↔ u ≤ 5 ∧ u + u ≤ t := Iff.rfl

reformulation boundedAfter : transformed := by
  epigraph t

example : GlobalEquivalence transformed boundedAfter := boundedAfter.equivalence

def shiftedSource :=
  problem (x y : ℝ)
    let loss := x ^ 2
    let offset := y
    let shift := offset + 1
    minimize loss
    subject to
      cap : loss ≤ 100

def shiftedCoverage : FeasibleSurjection shiftedSource
    (fun point : ℝ × ℝ => (point.1 + (point.2 + 1), point.2)) where
  preimage point := (point.1.1 - (point.1.2 + 1), point.1.2)
  rightInverse point := by
    apply Prod.ext
    · exact sub_add_cancel _ _
    · rfl

-- The replacement's aliases are declared after loss. Expanding their typed
-- values in the replacement avoids introducing forward references in loss.
reformulation shifted : shiftedSource := by
  substitute x := u + shift using shiftedCoverage

example : GlobalEquivalence shiftedSource shifted := shifted.equivalence
example (u y : ℝ) : shifted.objective (u, y) = (u + (y + 1)) ^ 2 := rfl

run_cmd do
  let env ← Lean.getEnv
  let some view := Morew.Syntax.getProblemView? env
      `MorewTest.Reformulation.LocalDefinitionSubstitution.shifted
    | Lean.throwError "substitution lost the target presentation"
  unless view.definitions.map (·.name.eraseMacroScopes) == #[`loss, `offset, `shift] do
    Lean.throwError "substitution lost or reordered model-local definitions"

def typedSource :=
  problem (x : ℝ)
    let equality : x = x := rfl
    let value : ℝ := x
    minimize value

def identityCoverage : FeasibleSurjection typedSource (fun u : ℝ => u) where
  preimage point := point.1
  rightInverse _ := rfl

reformulation typedTarget : typedSource := by
  substitute x := u using identityCoverage

example : GlobalEquivalence typedSource typedTarget := typedTarget.equivalence

def proofSource :=
  problem (x : ℝ)
    let identity : Real.log (Real.exp x) = x := Real.log_exp x
    let loss := Real.log x
    minimize loss
    subject to
      positive : 0 < x

-- Simplifying only the proof's annotation would turn it into exp u = exp u,
-- while Real.log_exp (exp u) still has its original, nondefinitional type.
reformulation proofTarget : proofSource := by
  substitute x := Real.exp u

example : GlobalEquivalence proofSource proofTarget := proofTarget.equivalence
example (u : ℝ) : proofTarget.objective u = u := by
  simp [proofTarget]

def chainedProofSource :=
  problem (x : ℝ)
    let loss := Real.log (Real.exp x)
    let identity : loss = x := Real.log_exp x
    let bounded : { y : ℝ // y = loss } := ⟨x, (Real.log_exp x).symm⟩
    minimize loss + bounded.val
    subject to
      positive : 0 < x

-- Preserve the whole dependent block so neither proofs nor subtype values
-- need transport when the decision binder is substituted.
reformulation chainedProofTarget : chainedProofSource := by
  substitute x := Real.exp u

example : GlobalEquivalence chainedProofSource chainedProofTarget :=
  chainedProofTarget.equivalence
example (u : ℝ) : chainedProofTarget.objective u = Real.exp u + Real.exp u := by
  simp [chainedProofTarget]

reformulation chainedProofBound : chainedProofSource := by
  substitute x := Real.exp u
  epigraph a at loss

example : GlobalEquivalence chainedProofSource chainedProofBound :=
  chainedProofBound.equivalence

example (u a : ℝ) : chainedProofBound.objective (u, a) = a + Real.exp u := by
  simp [chainedProofBound]

example (u a : ℝ) : chainedProofBound.feasible (u, a) ↔ Real.exp u ≤ a := by
  simp [chainedProofBound]

-- A preserved proof block keeps log(exp u) in the source presentation, while
-- terminal conic certification recognizes the checked affine objective u.
reformulation proofConic : proofSource := by
  substitute x := Real.exp u
  conic

example : GlobalEquivalence proofSource proofConic := proofConic.equivalence
example : Conic.Form proofConic := proofConic.conicForm
example : proofConic.conicForm.data.toProblem = proofConic :=
  proofConic.conicForm.represents

def fixedSubtypeSource :=
  problem (x : ℝ)
    let certified : { y : ℝ // Real.log (Real.exp y) = y } := ⟨x, Real.log_exp x⟩
    minimize Real.log certified.val
    subject to
      positive : 0 < x

-- This is data with a fixed type, not a proof-valued definition or a type
-- depending on x. Simplifying its predicate would invalidate its proof field.
reformulation fixedSubtypeTarget : fixedSubtypeSource := by
  substitute x := Real.exp u

example : GlobalEquivalence fixedSubtypeSource fixedSubtypeTarget :=
  fixedSubtypeTarget.equivalence
example (u : ℝ) : fixedSubtypeTarget.objective u = u := by
  simp [fixedSubtypeTarget]
example (u : ℝ) : fixedSubtypeTarget.feasible u := by
  simp [fixedSubtypeTarget]

/--
info: problem (u : ℝ)
  let certified : { y // Real.log (Real.exp y) = y } := ⟨Real.exp u, ⋯⟩
  minimize Real.log (↑certified : ℝ)
-/
#guard_msgs in
#printp fixedSubtypeTarget

structure EqualPair where
  left : ℝ
  right : ℝ
  equal : left = right

def fixedRecordSource :=
  problem (x : ℝ)
    let certified : EqualPair := ⟨Real.log (Real.exp x), x, Real.log_exp x⟩
    minimize Real.log certified.left
    subject to
      positive : 0 < x

-- The record's type does not change at all, but simplifying its first field
-- also changes the expected type of the stored equality proof.
reformulation fixedRecordTarget : fixedRecordSource := by
  substitute x := Real.exp u

example : GlobalEquivalence fixedRecordSource fixedRecordTarget :=
  fixedRecordTarget.equivalence
example (u : ℝ) : fixedRecordTarget.objective u = u := by
  simp [fixedRecordTarget]

reformulation fixedSubtypeConic : fixedSubtypeSource := by
  substitute x := Real.exp u
  epigraph t
  conic

example : GlobalEquivalence fixedSubtypeSource fixedSubtypeConic :=
  fixedSubtypeConic.equivalence
example : Conic.Form fixedSubtypeConic := fixedSubtypeConic.conicForm
example : fixedSubtypeConic.conicForm.data.toProblem = fixedSubtypeConic :=
  fixedSubtypeConic.conicForm.represents

def dependentValue (value : ℝ) (certified : { y : ℝ // y = value }) : ℝ :=
  certified.val

def inlineObjectiveSource :=
  problem (x : ℝ)
    let loss := Real.log (Real.exp x)
    minimize dependentValue loss ⟨x, (Real.log_exp x).symm⟩
    subject to
      positive : 0 < x

-- Checking just the simplified definitions would accept loss := exp u,
-- leaving the constructor's proof incompatible with its dependent argument.
reformulation inlineObjectiveTarget : inlineObjectiveSource := by
  substitute x := Real.exp u

example : GlobalEquivalence inlineObjectiveSource inlineObjectiveTarget :=
  inlineObjectiveTarget.equivalence
example (u : ℝ) : inlineObjectiveTarget.objective u = Real.exp u := rfl
example (u : ℝ) : inlineObjectiveTarget.feasible u := True.intro

def inlineMaxObjectiveSource :=
  problem (x : ℝ)
    let loss := Real.log (Real.exp x)
    maximize dependentValue loss ⟨x, (Real.log_exp x).symm⟩
    subject to
      positive : 0 < x

-- The complete-presentation check must preserve the maximization value type.
reformulation inlineMaxObjectiveTarget : inlineMaxObjectiveSource := by
  substitute x := Real.exp u

example : GlobalEquivalence inlineMaxObjectiveSource inlineMaxObjectiveTarget :=
  inlineMaxObjectiveTarget.equivalence
example (u : ℝ) : inlineMaxObjectiveTarget.objective u = Real.exp u := rfl

reformulation inlineObjectiveLifted : inlineObjectiveTarget := by
  epigraph t at (dependentValue loss ⟨Real.exp u, (Real.log_exp (Real.exp u)).symm⟩)

example : GlobalEquivalence inlineObjectiveTarget inlineObjectiveLifted :=
  inlineObjectiveLifted.equivalence
example (u t : ℝ) : inlineObjectiveLifted.objective (u, t) = t := rfl
example (u t : ℝ) : inlineObjectiveLifted.feasible (u, t) ↔ Real.exp u ≤ t := Iff.rfl

def inlineConstraintSource :=
  problem (x : ℝ)
    let loss := Real.log (Real.exp x)
    minimize Real.log x
    subject to
      positive : 0 < x
      cap : dependentValue loss ⟨x, (Real.log_exp x).symm⟩ ≤ 10

reformulation inlineConstraintTarget : inlineConstraintSource := by
  substitute x := Real.exp u

example : GlobalEquivalence inlineConstraintSource inlineConstraintTarget :=
  inlineConstraintTarget.equivalence
example (u : ℝ) : inlineConstraintTarget.objective u = u := by
  simp [inlineConstraintTarget]
example (u : ℝ) : inlineConstraintTarget.feasible u ↔ Real.exp u ≤ 10 := Iff.rfl

-- Continue in the same script as well as from a separately emitted target.
-- The whole presentation must remain coherent when the unchanged objective
-- also contains an expression that could have been simplified independently.
reformulation inlineConstraintLifted : inlineConstraintSource := by
  substitute x := Real.exp u
  epigraph t at (dependentValue loss ⟨Real.exp u, (Real.log_exp (Real.exp u)).symm⟩) in cap

example : GlobalEquivalence inlineConstraintSource inlineConstraintLifted :=
  inlineConstraintLifted.equivalence
example (u t : ℝ) : inlineConstraintLifted.objective (u, t) = u := by
  simp [inlineConstraintLifted]
example (u t : ℝ) : inlineConstraintLifted.feasible (u, t) ↔
    t ≤ 10 ∧ Real.exp u ≤ t := Iff.rfl

/-- error: substitution replacement uses model-local definition `loss`, which depends on the decision variable being replaced -/
#guard_msgs (substring := true) in
reformulation dependentReplacement : source := by
  substitute x := Real.exp u + loss

/-- error: decision variable `loss` conflicts with a model-local definition; choose a different decision name -/
#guard_msgs in
reformulation collidingBinder : source := by
  epigraph loss

run_cmd do
  let env ← Lean.getEnv
  for name in #[`dependentReplacement, `collidingBinder] do
    let full := `MorewTest.Reformulation.LocalDefinitionSubstitution ++ name
    if env.contains full || (Morew.Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed model-local substitution committed a declaration"

end
end MorewTest.Reformulation.LocalDefinitionSubstitution
