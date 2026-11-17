/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Rewrite
import MorewTest.ElabSupport
import MorewTest.Environment

/-! # CVaR epigraph certification for fixed parameters and affine losses -/

namespace MorewTest.Conic.Cvar

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew MorewTest.Affine
open scoped Matrix

noncomputable section

example (β : ℝ) (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1) :
    (Rewrite.cvarEpigraph β hn hβ).Auxiliary = (ℝ × (Fin n → ℝ)) := rfl

example (β : ℝ) (hn : 0 < n) (hβ : 0 ≤ β ∧ β < 1)
    (x u : Fin n → ℝ) (t τ : ℝ) :
    (Rewrite.cvarEpigraph β hn hβ).target x t (τ, u) ↔
      0 ≤ u ∧ x - (fun _ => τ) ≤ u ∧
        τ + (∑ i, u i) / ((n : ℝ) * (1 - β)) ≤ t := Iff.rfl

private def check (source : Expr) (rule? : Option Name := none) : MetaM Unit := do
  let before ← getMCtx
  let outcome ← match rule? with
    | none => Morew.Elab.Cone.Rewrite.planUnique source
    | some rule => Morew.Elab.Cone.Rewrite.planDeclaration source rule
  let result ← match outcome with
    | .ok result => pure result
    | .error error => throwError "CVaR epigraph was rejected: {error.reason}"
  assertExprMVarStateUnchanged before "CVaR planning"
  result.toResult.check source #[]
  let some auxiliary := result.auxiliary? | throwError "missing CVaR auxiliary variables"
  let auxiliary ← whnf auxiliary
  unless auxiliary.isAppOfArity ``Prod 2 do
    throwError "CVaR auxiliary is not a threshold and vector"
  unless ← isDefEq auxiliary.getAppArgs[0]! (mkConst ``Real) do
    throwError "CVaR threshold is not real"
  let .forallE _ index target _ ← whnf auxiliary.getAppArgs[1]!
    | throwError "CVaR slack is not a vector"
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 && target.isConstOf ``Real do
    throwError "CVaR slack has the wrong index or coordinate type"
  unless result.rowPredicates.size == 3 && result.certifiedRows.size == 3 do
    throwError "CVaR did not retain three certified rows"
  let vector ← mkAppM ``Morew.Conic.Cone.nonneg #[index.getAppArgs[0]!]
  let cones := #[vector, vector, mkConst ``Morew.Conic.Cone.nonnegScalar]
  for proof in #[result.certificate.expression, result.targetIff] do
    checkCompleteWithKernel proof "incomplete CVaR representation certificate"
  for predicate in result.rowPredicates, row in result.certifiedRows, expectedCone in cones do
    checkCompleteWithKernel row.constraint "incomplete CVaR cone constraint"
    checkCompleteWithKernel row.pointwiseIff "incomplete CVaR row certificate"
    let type ← whnf (← inferType row.constraint)
    let cone := mkAppN (mkConst ``Morew.Conic.Constraint.cone type.getAppFn.constLevels!)
      (type.getAppArgs ++ #[row.constraint])
    unless ← isDefEq cone expectedCone do
      throwError "CVaR produced the wrong cone"
    let expected ← withLocalDeclD `point result.nextDomain fun point => do
      let holds := mkAppN (mkConst ``Morew.Conic.Constraint.Holds type.getAppFn.constLevels!)
        (type.getAppArgs ++ #[row.constraint, point])
      mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
    unless ← isDefEq (← inferType row.pointwiseIff) expected do
      throwError "CVaR row certificate does not match its predicate"

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
  let .error _ := outcome | throwError "unsupported CVaR bound was accepted"
  assertExprMVarStateUnchanged before "failed CVaR planning"
  unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "failed CVaR planning changed declarations"

private def rejected (term : TSyntax `term) (parameters : Nat := 0)
    (rule? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameters fun _ source => reject source rule?

run_cmd liftTermElabM do
  for rule? in #[none, some ``Rewrite.cvarEpigraph] do
    expect (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar (1 / 2) p.1 ≤ p.2)) 0 rule?
    expect (← `(fun p : (Fin 3 → ℝ) × ℝ => p.2 ≥ Fn.cvar 0 p.1)) 0 rule?
    expect (← `(fun (n : Nat) (β : ℝ) (_hn : 0 < n) (_hβ : 0 ≤ β ∧ β < 1) =>
      fun p : (Fin n → ℝ) × ℝ => Fn.cvar β p.1 ≤ p.2)) 4 rule?
    expect (← `(fun (n : Nat) (β : ℝ) (_hn : 0 < n)
      (_hβ₀ : 0 ≤ β) (_hβ₁ : β < 1) =>
      fun p : (Fin n → ℝ) × ℝ => Fn.cvar β p.1 ≤ p.2)) 5 rule?
    expect (← `(fun (m n : Nat) (β : ℝ) (_hm : 0 < m)
      (_hβ : 0 ≤ β ∧ β < 1) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) =>
      fun p : (Fin n → ℝ) × ℝ => Fn.cvar β (A *ᵥ p.1 - b) ≤ p.2 + 1)) 7 rule?

run_cmd liftTermElabM do
  for rule? in #[none, some ``Rewrite.cvarEpigraph] do
    rejected (← `(fun (β : ℝ) =>
      fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar β p.1 ≤ p.2)) 1 rule?
    rejected (← `(fun (β : ℝ) (_hβ : β < 1) =>
      fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar β p.1 ≤ p.2)) 2 rule?
    rejected (← `(fun (β : ℝ) (_hβ : 0 ≤ β) =>
      fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar β p.1 ≤ p.2)) 2 rule?
    rejected (← `(fun (n : Nat) =>
      fun p : (Fin n → ℝ) × ℝ => Fn.cvar (1 / 2) p.1 ≤ p.2)) 1 rule?
    rejected (← `(fun p : (Fin 0 → ℝ) × ℝ => Fn.cvar (1 / 2) p.1 ≤ p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar 1 p.1 ≤ p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar (-1) p.1 ≤ p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => p.2 ≤ Fn.cvar (1 / 2) p.1)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar (1 / 2) p.1 = p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ =>
      Fn.cvar (1 / 2) (fun i => p.1 i ^ 2) ≤ p.2)) 0 rule?
    rejected (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar (1 / 2) p.1 ≤ p.2 ^ 2)) 0 rule?
    rejected (← `(fun (β : ℝ → ℝ) (_hβ : ∀ z, 0 ≤ β z ∧ β z < 1) =>
      fun p : ℝ × (Fin 3 → ℝ) × ℝ => Fn.cvar (β p.1) p.2.1 ≤ p.2.2)) 2 rule?

run_cmd liftTermElabM do
  let builder ← elaborate (← `(fun β : ℝ =>
    fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar β p.1 ≤ p.2))
  let missing ← mkFreshExprMVar (mkConst ``Real)
  for rule? in #[none, some ``Rewrite.cvarEpigraph] do
    reject (mkApp builder missing) rule?
    if ← missing.mvarId!.isAssigned then
      throwError "CVaR planning assigned an unresolved parameter"

section Removed

attribute [-morew_conic] Morew.Rewrite.cvarEpigraph

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : (Fin 3 → ℝ) × ℝ => Fn.cvar (1 / 2) p.1 ≤ p.2))
  reject source
  check source (some ``Rewrite.cvarEpigraph)

end Removed

end
end MorewTest.Conic.Cvar
