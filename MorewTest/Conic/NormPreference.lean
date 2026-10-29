/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support
import MorewTest.Environment
import Lean.Meta.Tactic.AuxLemma

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

-- Both built-in L2 candidates need an evidence-generated declaration. The
-- preferred SOC certificate must retain its own declaration while discarding
-- the power candidate's declaration; ambiguity must discard every candidate.
private def checkCandidateEvidence (ambiguous : Bool := false) : TermElabM Unit := do
  let expression ← elaborate (← `(fun (c : ℝ) (_ : c ≠ 0 ∧ True) =>
    fun z : (Fin 2 → ℝ) × ℝ => ‖WithLp.toLp 2 (fun i => z.1 i / c)‖ ≤ z.2))
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let assigned ← mkFreshExprMVar (mkConst ``Nat)
    assigned.mvarId!.assign (mkNatLit 7)
    let before ← getMCtx
    let environment ← getEnv
    let generated ← IO.mkRef (#[] : Array Name)
    let provider : Morew.Elab.Affine.EvidenceProvider := {
      nonzeroEvidence? := some fun obligation => do
        let proof ← mkAppM ``And.left #[parameters[1]!]
        unless ← isDefEq (← inferType proof) obligation do return none
        let proof ← mkLambdaFVars parameters proof
        let name ← mkAuxLemma [] (← inferType proof) proof (cache := false)
        generated.modify (·.push name)
        sentinel.mvarId!.assign (mkNatLit 19)
        return some (mkAppN (mkConst name) parameters)
    }
    let outcome ← Morew.Elab.Conic.Rewrite.planUnique source #[] provider
    let after ← getMCtx
    unless before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
      throwError "candidate evidence leaked scratch metavariables"
    for (id, value) in before.eAssignment.toList do
      unless after.eAssignment.find? id == some value do
        throwError "candidate evidence changed a caller assignment"
    for (id, _) in before.decls.toList do
      unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
        throwError "candidate evidence assigned a caller hole"
    if ← sentinel.mvarId!.isAssigned then
      throwError "candidate evidence retained the callback's caller assignment"
    unless (← instantiateMVars assigned) == mkNatLit 7 do
      throwError "candidate evidence discarded a caller assignment"
    let names ← generated.get
    unless names.size == (if ambiguous then 3 else 2) &&
        names.toList.eraseDups.length == names.size do
      throwError "expected a separate evidence declaration from every norm candidate: {names}"
    match outcome with
    | .error error =>
      unless ambiguous && (← error.reason.toString).contains "ambiguous exact conic rules" do
        throwError "unexpected evidence-backed norm rejection: {error.reason}"
      unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
        throwError "ambiguous norm candidates retained generated declarations"
    | .ok result =>
      if ambiguous then throwError "evidence-backed norm ambiguity was accepted"
      result.toResult.check source #[]
      unless result.auxiliary?.isNone && result.certifiedRows.size == 1 do
        throwError "evidence-backed L2 selection did not retain the SOC candidate"
      let certificates := #[result.certificate.expression, result.targetIff] ++
        result.certifiedRows.flatMap (fun row => #[row.constraint, row.pointwiseIff])
      for certificate in certificates do
        if certificate.hasMVar || certificate.hasSorry then
          throwError "evidence-backed norm certificate is incomplete"
        checkWithKernel certificate
      let referenced := names.filter fun name =>
        certificates.any fun certificate => (certificate.find? (·.isConstOf name)).isSome
      unless referenced.size == 1 do
        throwError "the SOC certificate must reference exactly its own evidence declaration"
      for name in names do
        unless (← getEnv).contains name == referenced.contains name do
          throwError "norm preference retained evidence from a discarded candidate: {name}"

run_cmd liftTermElabM do
  checkCandidateEvidence

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
  checkCandidateEvidence true
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
