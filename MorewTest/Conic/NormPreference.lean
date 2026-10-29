/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support
import MorewTest.Environment

/-!
# Narrow automatic preference for the native L2 representation

The SOC preference removes only the successful built-in power alternative.
Explicit selection, scoped registrations, and custom-rule ambiguity retain
their existing behavior. Every successful replacement checks its original
source, exact ordered rows, and kernel certificates.
-/

namespace MorewTest.Conic.NormPreference

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew Morew.Conic MorewTest.Affine
open scoped ENNReal

private def checkState (before : MetavarContext) (environment : Environment)
    (sentinel : Expr) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "norm rule selection leaked scratch metavariables"
  if ← sentinel.mvarId!.isAssigned then
    throwError "norm rule selection assigned a caller metavariable"
  unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
    throwError "norm rule selection changed the caller environment"

private def check (term : TSyntax `term) (expected : Array (TSyntax `term))
    (auxiliary : Bool := false) (rule? : Option Name := none) : TermElabM Unit := do
  let source ← elaborate term
  let sentinel ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let environment ← getEnv
  let result ← match rule? with
    | some rule => Morew.Elab.Conic.Rewrite.planDeclaration source rule
    | none => Morew.Elab.Conic.Rewrite.planUnique source
  checkState before environment sentinel
  let .ok result := result
    | match result with
      | .error error => throwError "expected a norm plan: {error.reason}"
      | .ok _ => throwError "unreachable"
  result.toResult.check source #[]
  unless result.auxiliary?.isSome == auxiliary do
    throwError "norm selection changed whether auxiliary decisions are introduced"
  unless result.rowPredicates.size == expected.size &&
      result.certifiedRows.size == expected.size do
    throwError "norm selection changed the expected number of rows"
  unless auxiliary do
    unless ← isDefEq result.nextDomain
        (← Morew.Elab.Rewrite.Plan.predicateDomain source) do
      throwError "the SOC norm representation changed the decision space"
  for actual in result.rowPredicates, expected in expected do
    unless ← isDefEq actual (← elaborate expected) do
      throwError "norm selection changed a generated row or its position: {actual}"
  for expression in #[result.certificate.expression, result.targetIff] ++
      result.certifiedRows.flatMap (fun row => #[row.constraint, row.pointwiseIff]) do
    if expression.hasMVar || expression.hasSorry then
      throwError "norm selection returned an incomplete certificate"
    checkWithKernel expression

private def reject (term : TSyntax `term) (message : String)
    (rule? : Option Name := none) (exact : Bool := true) : TermElabM Unit := do
  let source ← elaborate term
  let sentinel ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let environment ← getEnv
  let result ← match rule? with
    | some rule => Morew.Elab.Conic.Rewrite.planDeclaration source rule
    | none => Morew.Elab.Conic.Rewrite.planUnique source
  checkState before environment sentinel
  let .error error := result | throwError "expected norm selection to fail"
  let actual ← error.reason.toString
  unless if exact then actual == message else actual.contains message do
    throwError "unexpected norm-selection diagnostic: {actual}"

private def socRows : TermElabM (Array (TSyntax `term)) := do
  return #[← `(fun z : (Fin 2 → ℝ) × ℝ =>
    (z.2, z.1) ∈ (Cone.secondOrder 2).carrier)]

private def powerRows (exponent : TSyntax `term) : TermElabM (Array (TSyntax `term)) := do
  return #[← `(fun z : ((Fin 2 → ℝ) × ℝ) × (Fin 2 → ℝ) => 0 ≤ z.1.2),
    ← `(fun z : ((Fin 2 → ℝ) × ℝ) × (Fin 2 → ℝ) => (∑ i, z.2 i) ≤ z.1.2),
    ← `(fun z : ((Fin 2 → ℝ) × ℝ) × (Fin 2 → ℝ) =>
      ∀ i, (z.2 i, z.1.2, z.1.1 i) ∈ POW $exponent)]

run_cmd liftTermElabM do
  let source ← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 2 z.1‖ ≤ z.2)
  check source (← socRows)
  check source (← powerRows (← `((1 / 2 : ℝ)))) true
    (some ``Morew.Conic.Power.normEpigraph)

section
attribute [-morew_conic] Morew.Conic.SecondOrder.normEpigraph

run_cmd liftTermElabM do
  let source ← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 2 z.1‖ ≤ z.2)
  check source (← powerRows (← `((1 / 2 : ℝ)))) true
  check source (← socRows) false (some ``Morew.Conic.SecondOrder.normEpigraph)
end

-- Leaving the section restores the preferred automatic SOC representation.
run_cmd liftTermElabM do
  check (← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 2 z.1‖ ≤ z.2)) (← socRows)

noncomputable def customSOC {n : Nat} :
    EpigraphRepresentation (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖) :=
  Morew.Conic.SecondOrder.normEpigraph

section
attribute [local morew_conic] customSOC

-- The preference removes Power.normEpigraph, not the independent custom success.
run_cmd liftTermElabM do
  let source ← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 2 z.1‖ ≤ z.2)
  reject source
    "ambiguous exact conic rules: Morew.Conic.SecondOrder.normEpigraph, MorewTest.Conic.NormPreference.customSOC; select one with `using`"
  check source (← socRows) false (some ``customSOC)
  check source (← powerRows (← `((1 / 2 : ℝ)))) true
    (some ``Morew.Conic.Power.normEpigraph)
end

noncomputable def customPower {n : Nat} (p : ℝ≥0∞) (hp : 1 < p.toReal) :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp p v‖) :=
  Morew.Conic.Power.normEpigraph p hp

section
attribute [local morew_conic] customPower

-- Power remains an ordinary candidate, not a global fallback below custom rules.
run_cmd liftTermElabM do
  let source ← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 3 z.1‖ ≤ z.2)
  reject source
    "ambiguous exact conic rules: Morew.Conic.Power.normEpigraph, MorewTest.Conic.NormPreference.customPower; select one with `using`"
  check source (← powerRows (← `((1 / 3 : ℝ)))) true (some ``customPower)
  -- At L2 the preference removes only the built-in power declaration, not its alias.
  reject (← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 2 z.1‖ ≤ z.2))
    "ambiguous exact conic rules: Morew.Conic.SecondOrder.normEpigraph, MorewTest.Conic.NormPreference.customPower; select one with `using`"
end

-- This exact lift has an unnecessary nonlinear equality. Matching and exactness
-- succeed, but conic certification must reject its final generated row.
noncomputable def nonlinearPower {n : Nat} (p : ℝ≥0∞) (hp : 1 < p.toReal) :
    EpigraphRepresentation (fun v : Fin n → ℝ => ‖WithLp.toLp p v‖) where
  Auxiliary := (Fin n → ℝ) × ℝ
  target v t r := (Morew.Conic.Power.normEpigraph p hp).target v t r.1 ∧
    r.2 = ∑ i, (v i) ^ 2
  source_iff_exists v t := by
    constructor
    · intro h
      obtain ⟨r, hr⟩ := (Morew.Conic.Power.normEpigraph p hp).source_iff_exists v t |>.mp h
      exact ⟨(r, ∑ i, (v i) ^ 2), hr, rfl⟩
    · rintro ⟨r, hr, _⟩
      exact (Morew.Conic.Power.normEpigraph p hp).source_iff_exists v t |>.mpr ⟨r.1, hr⟩

section
attribute [local morew_conic] nonlinearPower

run_cmd liftTermElabM do
  let source ← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 3 z.1‖ ≤ z.2)
  reject source "generated row" (some ``nonlinearPower) false
  check source (← powerRows (← `((1 / 3 : ℝ)))) true
  check (← `(fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 2 z.1‖ ≤ z.2)) (← socRows)
end

end MorewTest.Conic.NormPreference
