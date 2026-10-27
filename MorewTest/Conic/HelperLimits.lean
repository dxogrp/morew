/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.HelperFixtures
import MorewTest.Affine.Support
import Lean.Meta.Tactic.AuxLemma

/-!
# Helper-expansion retries and failures at conic planning entry points

Budget failures return ordinary error results and roll back speculative evidence
before a later, independent planning call succeeds. Hidden finite evidence also
remains available when constructing a row after its coordinates have certified.
-/

namespace MorewTest.Conic.HelperLimits

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab MorewTest.Affine.HelperFixtures

-- Each operand or coordinate map can certify using its own helper's finite
-- evidence. Row construction then needs that evidence in the enclosing scope;
-- its synthesis failure must trigger the same retry as an explicit error result.
run_cmd Lean.Elab.Command.liftTermElabM do
  MorewTest.Affine.assertRow (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a b : ι → ℝ) => fun x : ι → ℝ => finiteDot e a x ≤ finiteDot e b x)) 4
  MorewTest.Affine.assertRow (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a b : ι → ℝ) => fun x : ι → ℝ =>
      (finiteDot e a x, (1 : ℝ), finiteDot e b x) ∈
        Morew.Conic.Cone.exponential.carrier)) 4

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasSorry then
    throwError "helper-budget regression did not fully elaborate its source"
  return expression

private def checkFailure (term : TSyntax `term) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let generated ← IO.mkRef (#[] : Array Name)
    let provider : Affine.EvidenceProvider := {
      nonzeroEvidence? := some fun obligation => do
        let proof ← mkAppM ``And.left #[parameters[1]!]
        unless ← isDefEq (← inferType proof) obligation do return none
        let closedProof ← mkLambdaFVars parameters proof
        let name ← mkAuxLemma [] (← inferType closedProof) closedProof (cache := false)
        generated.modify (·.push name)
        return some (mkAppN (mkConst name) parameters)
    }
    let callerHole ← mkFreshExprMVar (mkConst ``Nat)
    for _ in [:2] do
      let before ← getMCtx
      -- An escaping exception fails the regression instead of being accepted
      -- as equivalent to the public API's explicit error result.
      let .error error ← Conic.Rewrite.planUnique source #[] provider
        | throwError "conic rewriting exceeded the helper-depth limit"
      unless (← error.reason.toString).contains "maxExpansionDepth" do
        throwError "conic rewriting lost the budget diagnostic: {error.reason}"
      let after ← getMCtx
      unless before.mvarCounter == after.mvarCounter &&
          before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
        throwError "conic rewriting leaked speculative metavariables"
      if ← callerHole.mvarId!.isAssigned then
        throwError "conic rewriting assigned a caller metavariable"
      for name in ← generated.get do
        if (← getEnv).contains name then
          throwError "conic rewriting retained failed auxiliary evidence {name}"
    if (← generated.get).isEmpty then
      throwError "conic rewriting did not exercise evidence creation before failure"

private def checkSuccess (term : TSyntax `term) : TermElabM Unit := do
  let source ← elaborate term
  match ← Conic.Rewrite.planUnique source with
  | .ok _ => pure ()
  | .error error => throwError "conic rewriting failed after an independent limit failure: {error.reason}"

set_option morew.affine.maxExpansionDepth 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  checkFailure (← `(fun c : ℝ => fun (_h : c ≠ 0 ∧ True) =>
    fun x : ℝ => |x / c + nestedCost 2 1 x| ≤ 10))
  checkSuccess (← `(fun x : ℝ => |cost 2 1 x| ≤ 10))
  checkFailure (← `(fun c : ℝ => fun (_h : c ≠ 0 ∧ True) =>
    fun x : ℝ => (x / c + nestedCost 2 1 x) ^ 2 ≤ 10))
  checkSuccess (← `(fun x : ℝ => (cost 2 1 x) ^ 2 ≤ 10))
  checkFailure (← `(fun c : ℝ => fun (_h : c ≠ 0 ∧ True) =>
    fun x : ℝ => Real.exp (x / c + nestedCost 2 1 x) ≤ 10))
  checkSuccess (← `(fun x : ℝ => Real.exp (cost 2 1 x) ≤ 10))

end MorewTest.Conic.HelperLimits
