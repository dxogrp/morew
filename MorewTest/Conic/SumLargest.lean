/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Rewrite
import MorewTest.ElabSupport
import MorewTest.Environment

/-!
# Sum-largest epigraph certification

The threshold representation has two vector inequalities and one scalar bound,
including at empty dimension. Selection requires evidence for the fixed count.
-/

namespace MorewTest.Conic.SumLargest

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew MorewTest.Affine
open scoped Matrix

noncomputable section

example (k : Nat) (hk : k ≤ n) :
    (Rewrite.sumLargestEpigraph k hk).Auxiliary = (ℝ × (Fin n → ℝ)) := rfl

example (k : Nat) (hk : k ≤ n) (x u : Fin n → ℝ) (t τ : ℝ) :
    (Rewrite.sumLargestEpigraph k hk).target x t (τ, u) ↔
      0 ≤ u ∧ x - (fun _ => τ) ≤ u ∧ (k : ℝ) * τ + (∑ i, u i) ≤ t := Iff.rfl

example (x : Fin 0 → ℝ) (t : ℝ) :
    (∃ a, (Rewrite.sumLargestEpigraph 0 (le_refl 0)).target x t a) ↔ 0 ≤ t := by
  simp [Rewrite.sumLargestEpigraph]

example (x : Fin 0 → ℝ) :
    ¬ ∃ a, (Rewrite.sumLargestEpigraph 0 (le_refl 0)).target x (-1) a := by
  simp [Rewrite.sumLargestEpigraph]

private def check (source : Expr) (rule? : Option Name := none) : MetaM Unit := do
  let before ← getMCtx
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule
  let result ← match outcome with
    | .ok result => pure result
    | .error error => throwError "sum-largest epigraph was rejected: {error.reason}"
  assertMVarCountersUnchanged before "sum-largest planning changed caller metavariables"
  result.toResult.check source #[]
  let some auxiliary := result.auxiliary? | throwError "missing sum-largest auxiliary variables"
  let auxiliary ← whnf auxiliary
  unless auxiliary.isAppOfArity ``Prod 2 do
    throwError "sum-largest auxiliary is not a threshold and vector"
  unless ← isDefEq auxiliary.getAppArgs[0]! (mkConst ``Real) do
    throwError "sum-largest threshold is not real"
  let .forallE _ index target _ ← whnf auxiliary.getAppArgs[1]!
    | throwError "sum-largest slack is not a vector"
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 && target.isConstOf ``Real do
    throwError "sum-largest slack has the wrong index or coordinate type"
  unless result.rowPredicates.size == 3 && result.certifiedRows.size == 3 do
    throwError "sum-largest did not retain three certified rows"
  let vector ← mkAppM ``Morew.Conic.Cone.nonneg #[index.getAppArgs[0]!]
  let cones := #[vector, vector, mkConst ``Morew.Conic.Cone.nonnegScalar]
  for proof in #[result.certificate.expression, result.targetIff] do
    checkCompleteWithKernel proof "incomplete sum-largest representation certificate"
  for predicate in result.rowPredicates, row in result.certifiedRows, expectedCone in cones do
    checkCompleteWithKernel row.constraint "incomplete sum-largest cone constraint"
    checkCompleteWithKernel row.pointwiseIff "incomplete sum-largest row certificate"
    let type ← whnf (← inferType row.constraint)
    let cone := mkAppN (mkConst ``Morew.Conic.Constraint.cone type.getAppFn.constLevels!)
      (type.getAppArgs ++ #[row.constraint])
    unless ← isDefEq cone expectedCone do
      throwError "sum-largest produced the wrong cone"
    let expected ← withLocalDeclD `point result.nextDomain fun point => do
      let holds := mkAppN (mkConst ``Morew.Conic.Constraint.Holds type.getAppFn.constLevels!)
        (type.getAppArgs ++ #[row.constraint, point])
      mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
    unless ← isDefEq (← inferType row.pointwiseIff) expected do
      throwError "sum-largest row certificate does not match its predicate"

private def expect (term : TSyntax `term) (parameters : Nat := 0)
    (rule? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => check source rule?

private def reject (source : Expr) (rule? : Option Name := none) : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule
  let .error _ := outcome | throwError "unsupported sum-largest bound was accepted"
  assertMVarCountersUnchanged before "failed sum-largest planning changed caller metavariables"
  unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "failed sum-largest planning changed declarations"

private def rejected (term : TSyntax `term) (parameters : Nat := 0)
    (rule? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => reject source rule?

run_cmd liftTermElabM do
  for rule? in #[none, some ``Rewrite.sumLargestEpigraph] do
    expect (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 2 p.1 ≤ p.2)) 0 rule?
    expect (← `(fun p : (Fin 3 → ℝ) × ℝ => p.2 ≥ Fn.sumLargest 2 p.1)) 0 rule?
    expect (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 0 p.1 ≤ p.2)) 0 rule?
    expect (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 1 p.1 ≤ p.2)) 0 rule?
    expect (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 3 p.1 ≤ p.2)) 0 rule?
    expect (← `(fun p : (Fin 0 → ℝ) × ℝ => Fn.sumLargest 0 p.1 ≤ p.2)) 0 rule?
    expect (← `(fun x : Fin 0 → ℝ => Fn.sumLargest 0 x ≤ -1)) 0 rule?
    expect (← `(fun (n k : Nat) (_hk : k ≤ n) =>
      fun p : (Fin n → ℝ) × ℝ => Fn.sumLargest k p.1 ≤ p.2)) 3 rule?
    expect (← `(fun (n k : Nat) (_hk : k ≤ n ∧ True) =>
      fun p : (Fin n → ℝ) × ℝ => Fn.sumLargest k p.1 ≤ p.2)) 3 rule?
    expect (← `(fun n : Nat =>
      fun p : (Fin n → ℝ) × ℝ => Fn.sumLargest 0 p.1 ≤ p.2)) 1 rule?
    expect (← `(fun n : Nat =>
      fun p : (Fin n → ℝ) × ℝ => Fn.sumLargest n p.1 ≤ p.2)) 1 rule?
    expect (← `(fun (m n k : Nat) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
      (_hk : k ≤ m) => fun p : (Fin n → ℝ) × ℝ =>
        Fn.sumLargest k (A *ᵥ p.1 - b) ≤ p.2 + 1)) 6 rule?

run_cmd liftTermElabM do
  for rule? in #[none, some ``Rewrite.sumLargestEpigraph] do
    rejected (← `(fun (n k : Nat) =>
      fun p : (Fin n → ℝ) × ℝ => Fn.sumLargest k p.1 ≤ p.2)) 2 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 4 p.1 ≤ p.2)) 0 rule?
    rejected (← `(fun p : (Fin 0 → ℝ) × ℝ => Fn.sumLargest 1 p.1 ≤ p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => p.2 ≤ Fn.sumLargest 2 p.1)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 2 p.1 = p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ =>
      Fn.sumLargest 2 (fun i => p.1 i ^ 2) ≤ p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 2 p.1 ≤ p.2 ^ 2)) 0 rule?

run_cmd liftTermElabM do
  let builder ← elaborate (← `(fun k : Nat =>
    fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest k p.1 ≤ p.2))
  let missing ← mkFreshExprMVar (mkConst ``Nat)
  for rule? in #[none, some ``Rewrite.sumLargestEpigraph] do
    reject (mkApp builder missing) rule?
    if ← missing.mvarId!.isAssigned then
      throwError "sum-largest planning assigned an unresolved count"

section Removed

attribute [-morew_conic] Morew.Rewrite.sumLargestEpigraph

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.sumLargest 2 p.1 ≤ p.2))
  reject source
  check source (some ``Rewrite.sumLargestEpigraph)

end Removed

end
end MorewTest.Conic.SumLargest
