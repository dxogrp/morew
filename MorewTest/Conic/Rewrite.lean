/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.Support
import Lean.Meta.Tactic.AuxLemma
import MorewTest.Environment

/-!
# Certified exact-rule selection

Direct selection deliberately tests affine constant overlaps before the
terminal caller's affine-first shortcut. Other cases distinguish failed
candidate heads from fully certified registered rules.
-/

namespace MorewTest.Conic.Rewrite

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command
open Morew.Elab.Conic MorewTest.Affine

private def checkPrepared (source : Expr) (result : Plan.Result)
    (retained : Array Expr := #[]) : MetaM Nat := do
  result.toResult.check source retained
  let predicates := result.rowPredicates
  let rows := result.certifiedRows
  unless predicates.size == rows.size do throwError "missing certified replacement rows"
  for row in rows do
    for expression in #[row.constraint, row.pointwiseIff] do
      if expression.hasMVar || expression.hasSorry then
        throwError "incomplete automatic certificate"
      checkWithKernel expression
  return rows.size

private def expectUnique (stx : TSyntax `term) (count : Nat)
    (retained : Array Expr := #[]) : TermElabM Unit := do
  let source ← elaborate stx
  let before ← getMCtx
  let result ← Morew.Elab.Conic.Rewrite.planUnique source retained
  unless before.mvarCounter == (← getMCtx).mvarCounter &&
      before.lmvarCounter == (← getMCtx).lmvarCounter do
    throwError "automatic selection leaked scratch metavariables"
  let .ok result := result
    | match result with
      | .error error => throwError "expected a unique exact rule: {error.reason}"
      | .ok _ => throwError "unreachable selection result"
  unless (← checkPrepared source result retained) == count do
    throwError "unexpected automatic row count"

private def expectAmbiguous (stx : TSyntax `term) (names : Array String) :
    TermElabM Unit := do
  let source ← elaborate stx
  -- These overlaps are valid affine rows and should be bypassed by terminal
  -- conversion. They still exercise actual distinct native exact rules here.
  let .ok _ ← normalizeRow source | throwError "ambiguity fixture is not already affine"
  let before ← getMCtx
  let environment ← getEnv
  let .error error ← Morew.Elab.Conic.Rewrite.planUnique source
    | throwError "multiple exact rules were accepted as a unique match"
  let message ← error.reason.toString
  unless message.contains "ambiguous exact conic rules" do
    throwError "expected ambiguity, got {message}"
  for name in names do
    unless message.contains name do throwError "ambiguity omitted rule {name}: {message}"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "ambiguous selection leaked scratch metavariables"
  if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
    throwError "ambiguous selection leaked auxiliary declaration {name}"

run_cmd liftTermElabM do
  expectAmbiguous (← `(fun _ : ℝ => Real.exp 0 ≤ Real.log 2))
    #["Morew.Conic.Exponential.expEpigraph", "Morew.Conic.Exponential.logHypograph"]
  expectAmbiguous (← `(fun _ : ℝ => max (0 : ℝ) 1 ≤ min 2 3))
    #["Morew.Rewrite.maxEpigraph", "Morew.Rewrite.minHypograph"]
  expectUnique (← `(fun p : ℝ × ℝ => |(2 : ℝ)| ≤ min p.1 p.2)) 2
  expectUnique (← `(fun x : ℝ => x ^ 2 ≤ Real.log 2)) 1
  expectUnique (← `(fun x : ℝ => |x| ≤ Real.exp 2)) 2
  expectUnique (← `(fun x : ℝ => Real.exp x ≤ 3)) 1
  -- A logarithmic lower bound has one registered candidate; native and named
  -- composite registrations must not add unrelated certified alternatives.
  expectUnique (← `(fun t : ℝ => t ≤ Real.log 2)) 1
  let margin ← elaborate (← `(fun x : ℝ => 1 ≤ x))
  expectUnique (← `(fun x : ℝ => Real.exp 0 ≤ Real.log x)) 1 #[margin]
  expectUnique (← `(fun p : ℝ × ℝ => Morew.Fn.softplus p.1 ≤ p.2)) 2
  expectUnique (← `(fun p : ℝ × ℝ => Real.log (1 + Real.exp p.1) ≤ p.2)) 2
  expectUnique (← `(fun t : ℝ => Morew.Fn.relativeEntropy 0 2 ≤ t)) 1

-- Recognizing additional smooth atoms must not register new conic rules.
run_cmd liftTermElabM do
  for term in #[← `(fun x : ℝ => Real.sin x ≤ 1),
      ← `(fun x : ℝ => Real.cos x ≤ 1),
      ← `(fun x : ℝ => Real.sinh x ≤ 1),
      ← `(fun x : ℝ => Real.cosh x ≤ 1),
      ← `(fun x : ℝ => Real.tanh x ≤ 1)] do
    let source ← elaborate term
    if !(← Morew.Elab.Rewrite.Registry.candidates .conic source).isEmpty then
      throwError "a smooth-only atom became an exponential cone candidate"
    let .error _ ← Morew.Elab.Conic.Rewrite.planUnique source
      | throwError "a smooth-only atom acquired an automatic conic rule"

run_cmd liftTermElabM do
  let source ← elaborate (← `(fun p : ℝ × ℝ => p.2 ≤ Real.log p.1))
  let .error error ← Morew.Elab.Conic.Rewrite.planUnique source
    | throwError "logarithm without a retained margin was accepted"
  unless (← error.reason.toString).contains "positive constant margin" do
    throwError "automatic selection lost its domain diagnostic: {error.reason}"
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => Real.exp x ≤ c))
  let hole ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let .error _ ← Morew.Elab.Conic.Rewrite.planUnique (mkApp builder hole)
    | throwError "automatic selection accepted unresolved input"
  unless before.mvarCounter == (← getMCtx).mvarCounter do
    throwError "failed selection leaked scratch metavariables"
  if ← hole.mvarId!.isAssigned then throwError "automatic selection assigned a caller hole"

/-- Evidence-generated auxiliary declarations survive only an accepted plan. -/
private def checkEvidenceLifetime (stx : TSyntax `term) (success : Bool) :
    TermElabM Unit := do
  let expression ← elaborate stx
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let generated ← IO.mkRef (#[] : Array Name)
    let provider : Morew.Elab.Affine.EvidenceProvider := {
      nonzeroEvidence? := some fun obligation => do
        let proof ← mkAppM ``And.left #[parameters[1]!]
        unless ← isDefEq (← inferType proof) obligation do return none
        let proof ← mkLambdaFVars parameters proof
        let name ← mkAuxLemma [] (← inferType proof) proof (cache := false)
        generated.modify (·.push name)
        return some (mkAppN (mkConst name) parameters)
    }
    let result ← Morew.Elab.Conic.Rewrite.planUnique source #[] provider
    match result with
    | .ok result =>
      unless success do throwError "nonlinear replacement was accepted"
      discard <| checkPrepared source result
    | .error error =>
      if success then throwError "evidence-backed replacement failed: {error.reason}"
    let names ← generated.get
    if names.isEmpty then throwError "test did not exercise evidence-generated declarations"
    for name in names do
      unless (← getEnv).contains name == success do
        throwError "automatic selection mishandled auxiliary declaration {name}"

run_cmd liftTermElabM do
  checkEvidenceLifetime (← `(fun (c : ℝ) (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => |x / c| ≤ 1)) true
  checkEvidenceLifetime (← `(fun (c : ℝ) (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => max (x / c) (x * x) ≤ 1)) false

end MorewTest.Conic.Rewrite
