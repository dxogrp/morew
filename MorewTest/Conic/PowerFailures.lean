/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support
import MorewTest.Environment

/-!
# Boundaries of exact power-cone certification

Rejections retain their caller's metavariables and declarations. Positive
controls distinguish unsupported powers from failures of the test setup.
-/

namespace MorewTest.Conic.PowerFailures

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Conic MorewTest.Affine

private def reject (source : Expr) (retained : Array Expr := #[])
    (name? : Option Name := none) (fragment : String := "") : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let result ← match name? with
    | none => Morew.Elab.Conic.Rewrite.planUnique source retained
    | some name => Morew.Elab.Conic.Rewrite.planDeclaration source name retained
  let .error error := result | throwError "unsupported power bound was accepted: {source}"
  let diagnostic ← error.reason.toString
  if diagnostic.isEmpty || (!fragment.isEmpty && !diagnostic.contains fragment) then
    throwError "unexpected power diagnostic: {diagnostic}"
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "failed power planning leaked metavariables"
  unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "failed power planning changed declarations"

private def check (source : Expr) (retained : Array Expr := #[])
    (name? : Option Name := none) : MetaM Unit := do
  let result ← match name? with
    | none => Morew.Elab.Conic.Rewrite.planUnique source retained
    | some name => Morew.Elab.Conic.Rewrite.planDeclaration source name retained
  let .ok result := result
    | match result with
      | .error error => throwError "power control was rejected: {error.reason}"
      | .ok _ => throwError "unreachable"
  result.toResult.check source retained
  checkWithKernel result.certificate.expression
  for row in result.certifiedRows do
    checkWithKernel row.constraint
    checkWithKernel row.pointwiseIff

private def rejected (term : TSyntax `term) (retained : Array Expr := #[])
    (parameterCount : Nat := 0) (name? : Option Name := none)
    (fragment : String := "") : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source =>
    reject source retained name? fragment

run_cmd liftTermElabM do
  let domain ← elaborate (← `(fun p : ℝ × ℝ => 0 ≤ p.1))
  let positive ← elaborate (← `(fun p : ℝ × ℝ => 1 ≤ p.1))
  let source ← elaborate (← `(fun p : ℝ × ℝ => Real.rpow p.1 (3 / 2) ≤ p.2))
  check source #[domain]
  reject source -- The selected inequality cannot establish its own base domain.
  rejected (← `(fun p : ℝ × ℝ => Real.rpow p.1 (-1 / 2) ≤ p.2)) #[domain]
  check (← elaborate (← `(fun p : ℝ × ℝ => Real.rpow p.1 (-1 / 2) ≤ p.2)))
    #[positive]
  -- Wrong polarities and nonlinear equality have no automatic exact rule.
  rejected (← `(fun p : ℝ × ℝ => p.2 ≤ Real.rpow p.1 (3 / 2))) #[domain]
  rejected (← `(fun p : ℝ × ℝ => Real.rpow p.1 (1 / 2) ≤ p.2)) #[domain]
  rejected (← `(fun p : ℝ × ℝ => Real.rpow p.1 (3 / 2) = p.2)) #[domain]
  -- A nonlinear bound or coordinate cannot be certified as an affine cone map.
  rejected (← `(fun p : ℝ × ℝ => Real.rpow p.1 (3 / 2) ≤ p.2 ^ (2 : ℕ)))
    #[domain]
  let nonlinearDomain ← elaborate (← `(fun p : ℝ × ℝ => 0 ≤ p.1 ^ (2 : ℕ)))
  rejected (← `(fun p : ℝ × ℝ => Real.rpow (p.1 ^ (2 : ℕ)) (3 / 2) ≤ p.2))
    #[nonlinearDomain]
  -- Independent exact hypotheses are allowed; symbolic implication search is not.
  rejected (← `(fun (q : ℝ) => fun t : ℝ => Real.rpow 2 q ≤ t))
    (parameterCount := 1)
  rejected (← `(fun (q : ℝ) (_hq : 2 < q) => fun t : ℝ => Real.rpow 2 q ≤ t))
    (parameterCount := 2)
  -- Explicit selection never falls back to the valid positive-power rule.
  reject source #[domain] (some ``Morew.Conic.Power.rpowNegativeEpigraph)
  -- The zero value of totalized negative powers is not a positive-domain model.
  rejected (← `(fun t : ℝ => Real.rpow 0 (-1 / 2) ≤ t))

private noncomputable def hiddenPower (x : ℝ) : ℝ := Real.rpow x (3 / 2)

run_cmd liftTermElabM do
  let domain ← elaborate (← `(fun p : ℝ × ℝ => 0 ≤ p.1))
  rejected (← `(fun p : ℝ × ℝ => hiddenPower p.1 ≤ p.2)) #[domain]
  -- The canonical native operation is required, not merely the same surface token.
  rejected (← `(fun [HPow ℝ ℝ ℝ] => fun p : ℝ × ℝ => p.1 ^ (3 / 2 : ℝ) ≤ p.2))
    #[domain] (parameterCount := 1)
  rejected (← `(fun [LE ℝ] => fun p : ℝ × ℝ => Real.rpow p.1 (3 / 2) ≤ p.2))
    #[domain] (parameterCount := 1)

section Removed

attribute [-morew_conic] Morew.Conic.Power.rpowEpigraph

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : ℝ × ℝ => Real.rpow p.1 (3 / 2) ≤ p.2))
  let domain ← elaborate (← `(fun p : ℝ × ℝ => 0 ≤ p.1))
  reject source #[domain]
  check source #[domain] (some ``Morew.Conic.Power.rpowEpigraph)

end Removed

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : ℝ × ℝ => Real.rpow p.1 (3 / 2) ≤ p.2))
  let domain ← elaborate (← `(fun p : ℝ × ℝ => 0 ≤ p.1))
  check source #[domain]

private def rejectRow (source : Expr) (fragment : String := "") : MetaM Unit := do
  let before ← getMCtx
  let environment ← getEnv
  let .error error ← Morew.Elab.Conic.normalizeRow source (label? := some `power_row)
    | throwError "unsupported power membership was accepted: {source}"
  let diagnostic ← error.reason.toString
  unless diagnostic.contains "power_row" &&
      (fragment.isEmpty || diagnostic.contains fragment) do
    throwError "power membership lost its diagnostic context: {diagnostic}"
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter &&
      MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "failed power membership changed caller state"

run_cmd liftTermElabM do
  assertRow (← `(fun x : ℝ => (x, 1, x + 1) ∈ POW (1 / 2 : ℝ)))
  rejectRow (← elaborate (← `(fun x : ℝ => (x, 1, x) ∈ POW (0 : ℝ))))
    "required"
  rejectRow (← elaborate (← `(fun x : ℝ => (x, 1, x) ∈ POW (1 : ℝ))))
    "required"
  rejectRow (← elaborate (← `(fun x : ℝ => (x, 1, x) ∈ POW x))) "decision"
  rejectRow (← elaborate (← `(fun x : ℝ => (x ^ (2 : ℕ), 1, x) ∈ POW (1 / 2 : ℝ))))
  rejectRow (← elaborate (← `(fun x : ℝ =>
    ∀ _i : Fin 0, (x, 1, x) ∈ POW (1 / 2 : ℝ))))
  let altered ← elaborate (← `(fun [Membership (ℝ × ℝ × ℝ) (Set (ℝ × ℝ × ℝ))] =>
    fun x : ℝ => (x, 1, x) ∈ POW (1 / 2 : ℝ)))
  lambdaBoundedTelescope altered 1 fun _ source => rejectRow source "membership"

-- Holes hidden in local declarations cannot be solved speculatively to make a
-- power-cone parameter valid. Placeholder evidence must never enter certificates.
run_cmd liftTermElabM do
  let family ← elaborate (← `(fun (α : ℝ) => fun x : ℝ => (x, 1, x) ∈ POW α))
  let hole ← mkFreshExprMVar (mkConst ``Real)
  rejectRow (mkApp family hole) "unresolved"
  withLetDecl `hiddenExponent (mkConst ``Real) hole fun exponent =>
    rejectRow (mkApp family exponent) "unresolved"
  if ← hole.mvarId!.isAssigned then throwError "power membership assigned the caller's exponent"
  let range ← elaborate (← `(fun α : ℝ => 0 < α ∧ α < 1))
  let bundled ← elaborate (← `(fun (α : ℝ) (h : 0 < α ∧ α < 1) =>
    fun x : ℝ => (x, 1, x) ∈ (Cone.power α h).carrier))
  withLocalDeclD `α (mkConst ``Real) fun exponent => do
    let obligation := range.beta #[exponent]
    let placeholder ← mkSorry obligation true
    rejectRow (mkAppN bundled #[exponent, placeholder])
    withLetDecl `hiddenRange obligation placeholder fun hidden => do
      rejectRow (mkApp family exponent)
      rejectRow (mkAppN bundled #[exponent, hidden])

end MorewTest.Conic.PowerFailures
