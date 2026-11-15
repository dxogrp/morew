/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Rewrite
import MorewTest.ElabSupport
import MorewTest.Environment

/-!
# Huber epigraph certification

The scalar rule produces one rotated cone and three affine inequalities.
The finite-sum rule combines the squares into one cone and retains two vector
inequalities. These checks cover parameter evidence, affine residuals, and rejected bounds.
-/

namespace MorewTest.Conic.Huber

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Conic MorewTest.Affine
open scoped Matrix

noncomputable section

example (M : ℝ) (hM : 0 ≤ M) (x t z s r : ℝ) :
    (SecondOrder.huberEpigraph M hM).target x t (z, s, r) ↔
      (s, 1 / 2, ![z]) ∈ RSOC 1 ∧ -r ≤ x - z ∧ x - z ≤ r ∧
        s + 2 * M * r ≤ t := Iff.rfl

example (x t : ℝ) :
    (∃ u, (SecondOrder.huberEpigraph 0 (le_refl 0)).target x t u) ↔ 0 ≤ t := by
  simpa only [Fn.huber_zero_left] using
    (SecondOrder.huberEpigraph 0 (le_refl 0)).source_iff_exists x t |>.symm

private def check (source : Expr) (rule? : Option Name := none)
    (rows : Nat := 4) : MetaM Unit := do
  let before ← getMCtx
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule
  let result ← match outcome with
    | .ok result => pure result
    | .error error => throwError "Huber epigraph was rejected: {error.reason}"
  assertMVarCountersUnchanged before "Huber planning changed caller metavariables"
  result.toResult.check source #[]
  let some actual := result.auxiliary? | throwError "missing Huber auxiliary variables"
  if rows == 4 then
    let auxiliary ← mkAppM ``Prod #[mkConst ``Real,
      ← mkAppM ``Prod #[mkConst ``Real, mkConst ``Real]]
    unless ← isDefEq actual auxiliary do throwError "wrong scalar Huber auxiliary type"
  unless result.rowPredicates.size == rows && result.certifiedRows.size == rows do
    throwError "wrong number of certified Huber rows"
  for proof in #[result.certificate.expression, result.targetIff] do
    checkCompleteWithKernel proof "incomplete Huber representation certificate"
  for predicate in result.rowPredicates, row in result.certifiedRows do
    checkCompleteWithKernel row.constraint "incomplete Huber cone constraint"
    checkCompleteWithKernel row.pointwiseIff "incomplete Huber row certificate"
    let type ← whnf (← inferType row.constraint)
    let expected ← withLocalDeclD `point result.nextDomain fun point => do
      let holds := mkAppN (mkConst ``Morew.Conic.Constraint.Holds type.getAppFn.constLevels!)
        (type.getAppArgs ++ #[row.constraint, point])
      mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
    unless ← isDefEq (← inferType row.pointwiseIff) expected do
      throwError "Huber row certificate does not match its predicate"

private def expect (term : TSyntax `term) (parameters : Nat := 0)
    (rule? : Option Name := none) (rows : Nat := 4) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => check source rule? rows

private def reject (source : Expr) (retained : Array Expr := #[])
    (rule? : Option Name := none) : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source retained
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule retained
  let .error _ := outcome | throwError "unsupported Huber bound was accepted"
  assertMVarCountersUnchanged before "failed Huber planning changed caller metavariables"
  unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "failed Huber planning changed declarations"

private def rejected (term : TSyntax `term) (parameters : Nat := 0)
    (rule? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => reject source #[] rule?

run_cmd liftTermElabM do
  expect (← `(fun p : ℝ × ℝ => Fn.huber 2 (2 * p.1 - 1) ≤ p.2 + 3))
  expect (← `(fun p : ℝ × ℝ => p.2 ≥ Fn.huber 2 p.1))
  expect (← `(fun p : ℝ × ℝ => Fn.huber 0 p.1 ≤ p.2))
  expect (← `(fun p : ℝ × ℝ => Fn.huber 2 p.1 ≤ p.2))
    (rule? := some ``SecondOrder.huberEpigraph)
  expect (← `(fun (M : ℝ) (_hM : 0 ≤ M) =>
    fun p : ℝ × ℝ => Fn.huber M (2 * p.1 - 1) ≤ p.2)) 2
  expect (← `(fun (M : ℝ) (_hM : 0 ≤ M) =>
    fun p : ℝ × ℝ => Fn.huber M p.1 ≤ p.2)) 2
    (some ``SecondOrder.huberEpigraph)
  expect (← `(fun (n : Nat) (A : Matrix (Fin 1) (Fin n) ℝ) (b : Fin 1 → ℝ)
    (M : ℝ) (_hM : 0 ≤ M) => fun p : (Fin n → ℝ) × ℝ =>
      Fn.huber M ((A *ᵥ p.1 - b) 0) ≤ p.2)) 5

run_cmd liftTermElabM do
  rejected (← `(fun M : ℝ => fun p : ℝ × ℝ => Fn.huber M p.1 ≤ p.2)) 1
  rejected (← `(fun M : ℝ => fun p : ℝ × ℝ => Fn.huber M p.1 ≤ p.2)) 1
    (some ``SecondOrder.huberEpigraph)
  rejected (← `(fun p : ℝ × ℝ => Fn.huber (-1) p.1 ≤ p.2))
  rejected (← `(fun p : ℝ × ℝ => p.2 ≤ Fn.huber 2 p.1))
  rejected (← `(fun p : ℝ × ℝ => Fn.huber 2 p.1 = p.2))
  rejected (← `(fun p : ℝ × ℝ => Fn.huber 2 (p.1 ^ 2) ≤ p.2))
  rejected (← `(fun p : ℝ × ℝ => Fn.huber 2 p.1 ≤ p.2 ^ 2))
  let source ← elaborate (← `(fun p : ℝ × ℝ × ℝ => Fn.huber p.1 p.2.1 ≤ p.2.2))
  let retained ← elaborate (← `(fun p : ℝ × ℝ × ℝ => 0 ≤ p.1))
  reject source #[retained]
  reject source #[retained] (some ``SecondOrder.huberEpigraph)

section Removed

attribute [-morew_conic] Morew.Conic.SecondOrder.huberEpigraph

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : ℝ × ℝ => Fn.huber 2 p.1 ≤ p.2))
  reject source
  check source (some ``SecondOrder.huberEpigraph)

end Removed

/-! Finite sums use the same parameter evidence, including at empty dimension. -/

example (M : ℝ) (hM : 0 ≤ M) :
    (SecondOrder.sumHuberEpigraph (n := n) M hM).Auxiliary =
      ((Fin n → ℝ) × (Fin n → ℝ)) := rfl

example (M : ℝ) (hM : 0 ≤ M) (v z u : Fin n → ℝ) (t : ℝ) :
    (SecondOrder.sumHuberEpigraph M hM).target v t (z, u) ↔
      (t - 2 * M * (∑ i, u i), 1 / 2, z) ∈ RSOC n ∧
        -u ≤ v - z ∧ v - z ≤ u := Iff.rfl

example (v : Fin n → ℝ) (t : ℝ) :
    (∃ a, (SecondOrder.sumHuberEpigraph 0 (le_refl 0)).target v t a) ↔ 0 ≤ t := by
  simpa using (SecondOrder.sumHuberEpigraph 0 (le_refl 0)).source_iff_exists v t |>.symm

example (M : ℝ) (hM : 0 ≤ M) (v : Fin 0 → ℝ) (t : ℝ) :
    (∃ a, (SecondOrder.sumHuberEpigraph M hM).target v t a) ↔ 0 ≤ t := by
  simpa using (SecondOrder.sumHuberEpigraph M hM).source_iff_exists v t |>.symm

run_cmd liftTermElabM do
  for rule? in #[none, some ``SecondOrder.sumHuberEpigraph] do
    expect (← `(fun (m n : Nat) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
      (M : ℝ) (_hM : 0 ≤ M) => fun p : (Fin n → ℝ) × ℝ =>
        (∑ i, Fn.huber M ((A *ᵥ p.1 - b) i)) ≤ p.2)) 6 rule? 3
    expect (← `(fun p : (Fin 2 → ℝ) × ℝ =>
      (∑ i, Fn.huber 0 (p.1 i)) ≤ p.2)) 0 rule? 3
    expect (← `(fun p : (Fin 0 → ℝ) × ℝ =>
      (∑ i, Fn.huber 2 (p.1 i)) ≤ p.2)) 0 rule? 3
    rejected (← `(fun M : ℝ => fun p : (Fin 2 → ℝ) × ℝ =>
      (∑ i, Fn.huber M (p.1 i)) ≤ p.2)) 1 rule?
    rejected (← `(fun p : (Fin 2 → ℝ) × ℝ =>
      p.2 ≤ ∑ i, Fn.huber 2 (p.1 i))) 0 rule?
    rejected (← `(fun p : (Fin 2 → ℝ) × ℝ =>
      (∑ i, Fn.huber 2 (p.1 i ^ 2)) ≤ p.2)) 0 rule?
    let source ← elaborate (← `(fun p : ℝ × (Fin 2 → ℝ) × ℝ =>
      (∑ i, Fn.huber p.1 (p.2.1 i)) ≤ p.2.2))
    let retained ← elaborate (← `(fun p : ℝ × (Fin 2 → ℝ) × ℝ => 0 ≤ p.1))
    reject source #[retained] rule?

end
end MorewTest.Conic.Huber
