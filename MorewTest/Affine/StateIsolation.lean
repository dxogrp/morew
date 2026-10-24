/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic
import Lean.Meta.Tactic.AuxLemma

/-!
# Affine recognition state and callback-generated proofs

Evidence callbacks can use Lean's auxiliary-theorem API. Their declarations
must remain available in successful certificates, including through nested row
and objective adapters, while failed recognition rolls them back.
-/

namespace MorewTest.Affine.StateIsolation

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab

private noncomputable def quotientHelper (c x : ℝ) : ℝ := x / c

private inductive EntryPoint where
  | affine
  | row
  | objective
  deriving Repr

private def recognize (entry : EntryPoint) (source : Expr) (config : Affine.Config) :
    MetaM (Except Affine.AffineError (Array Expr)) := do
  match entry with
  | .affine =>
    return (← Affine.reifyAffine source config).map fun result =>
      #[result.map, result.pointwiseEquality]
  | .row =>
    return (← Conic.normalizeRow source config).map fun result =>
      #[result.constraint, result.pointwiseIff]
  | .objective =>
    let real := Lean.mkConst ``Real
    let presentation : Reformulation.PresentationState := {
      sense := .maximize
      domainType := real
      valueType := mkApp (Lean.mkConst ``OrderDual [Level.zero]) real
      binders := #[{ name := `x, type := real }]
      objective := source
    }
    return (← Conic.reifyObjective presentation config).map fun result =>
      #[result.map, result.pointwiseEquality]

private def withAuxEvidence (term : TSyntax `term) (cache : Bool)
    (action : Expr → Affine.Config → IO.Ref (Array Name) → TermElabM Unit) :
    TermElabM Unit := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasSorry then
    throwError "state regression did not fully elaborate its source"
  lambdaBoundedTelescope expression 2 fun parameters source => do
    let generated ← IO.mkRef (#[] : Array Name)
    let config : Morew.Elab.Affine.Config := {
      nonzeroEvidence? := some fun obligation => do
        let proof ← mkAppM ``And.left #[parameters[1]!]
        unless ← isDefEq (← inferType proof) obligation do return none
        -- Auxiliary declarations must be closed over the external parameters.
        let closedProof ← mkLambdaFVars parameters proof
        let name ← mkAuxLemma [] (← inferType closedProof) closedProof
          (cache := cache)
        generated.modify (·.push name)
        -- Exercise scratch metavariables inside the callback as well.
        let scratch ← mkFreshExprMVar obligation
        scratch.mvarId!.assign (mkAppN (Lean.mkConst name) parameters)
        return some (← instantiateMVars scratch)
    }
    action source config generated

private def checkUnchanged (before : MetavarContext) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "affine recognition leaked scratch metavariables"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "affine recognition changed a caller metavariable assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "affine recognition assigned an unresolved caller metavariable"

private def checkSuccess (entry : EntryPoint) (term : TSyntax `term)
    (cache : Bool := true) : TermElabM Unit :=
  withAuxEvidence term cache fun source config generated => do
    let unresolved ← mkFreshExprMVar (Lean.mkConst ``Nat)
    let assigned ← mkFreshExprMVar (Lean.mkConst ``Nat)
    assigned.mvarId!.assign (mkNatLit 7)
    for _ in [:3] do
      let before ← getMCtx
      let result ← recognize entry source config
      let .ok expressions := result
        | match result with
          | .error error => throwError
              "callback-generated evidence was rejected by {repr entry}: {error.reason}"
          | .ok _ => throwError "unreachable recognition result"
      checkUnchanged before
      for expression in expressions do
        if expression.hasMVar || expression.hasSorry then
          throwError "recognition returned an incomplete certificate"
        checkWithKernel expression
      let names ← generated.get
      for name in names do
        unless (← getEnv).contains name do
          throwError "successful recognition discarded auxiliary theorem {name}"
    if ← unresolved.mvarId!.isAssigned then
      throwError "recognition assigned a caller metavariable"
    unless (← instantiateMVars assigned) == mkNatLit 7 do
      throwError "recognition discarded a caller metavariable assignment"
    let names ← generated.get
    unless names.size == 3 do
      throwError "test did not invoke evidence callback on every recognition"
    if !cache && names.toList.eraseDups.length != 3 then
      throwError "uncached auxiliary declarations reused a generated name"

private def checkFailure (entry : EntryPoint) (term : TSyntax `term)
    (cache : Bool := true) : TermElabM Unit :=
  withAuxEvidence term cache fun source config generated => do
    let unresolved ← mkFreshExprMVar (Lean.mkConst ``Nat)
    let assigned ← mkFreshExprMVar (Lean.mkConst ``Nat)
    assigned.mvarId!.assign (mkNatLit 7)
    -- A second attempt also checks that the auxiliary-lemma cache rolled back.
    for _ in [:2] do
      let before ← getMCtx
      let .error error ← recognize entry source config
        | throwError "nonlinear expression was accepted"
      checkUnchanged before
      unless (← error.reason.toString).contains "both factors of multiplication" do
        throwError "recognition failed before reaching the nonlinear operand: {error.reason}"
      for name in (← generated.get) do
        if (← getEnv).contains name then
          throwError "failed recognition retained auxiliary theorem {name}"
    if ← unresolved.mvarId!.isAssigned then
      throwError "failed recognition assigned a caller metavariable"
    unless (← instantiateMVars assigned) == mkNatLit 7 do
      throwError "failed recognition discarded a caller assignment"
    unless (← generated.get).size == 2 do
      throwError "failure did not occur after auxiliary theorem creation"

run_cmd Lean.Elab.Command.liftTermElabM do
  let nonlinear ← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => x / c + x * x)
  let nonlinearRow ← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => x / c ≤ x * x)
  -- Start with failures so no cached successful proof predates these calls.
  checkFailure .affine nonlinear
  checkFailure .row nonlinearRow
  checkFailure .objective nonlinear
  let affine ← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) => fun x : ℝ => x / c)
  let row ← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) => fun x : ℝ => x / c ≤ 1)
  checkSuccess .affine affine
  -- Fresh declarations ensure each outer adapter must retain its nested
  -- recognizer's environment changes, rather than reusing the affine proof.
  checkSuccess .row row false
  checkSuccess .objective affine false
  checkSuccess .affine affine false

/-! Helper fallback preserves the same transaction boundary as direct recognition. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let affine ← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => quotientHelper c x)
  let row ← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => quotientHelper c x ≤ 1)
  let nonlinear ← `(fun c : ℝ => fun (_ : c ≠ 0 ∧ True) =>
    fun x : ℝ => quotientHelper c x + x * x)
  checkFailure .affine nonlinear false
  checkFailure .objective nonlinear false
  checkSuccess .affine affine false
  checkSuccess .row row false
  checkSuccess .objective affine false

end MorewTest.Affine.StateIsolation
