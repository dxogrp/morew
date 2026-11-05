/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Evidence.Sign
import MorewTest.ElabSupport
import MorewTest.Environment

/-!
# Nonnegative membership recognition without conic planning

Sign evidence checks exact cone coordinates and instances without importing the
affine row certifier. Both successful and failed attempts preserve caller state.
-/

assert_not_exists Morew.Elab.Conic.normalizeRow Morew.Elab.Conic.Plan.Result
  Morew.Elab.Conic.Rewrite.planUnique Morew.Conic.Spectral.normNuc_le_iff
  Morew.Conic.LogDet.hypograph_iff

namespace MorewTest.Conic.Nonnegative

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command Morew

private def check (term : TSyntax `term) (accepted : Bool) (parameters : Nat := 0) :
    TermElabM Unit := do
  let source ← MorewTest.Affine.elaborate term
  lambdaBoundedTelescope source parameters fun _ source =>
    lambdaTelescope source fun points body => do
      unless points.size == 1 do throwError "expected one decision point"
      let before ← getMCtx
      let environment ← getEnv
      let result ← Elab.Conic.nonnegativeValue? points[0]! body
      unless result.isSome == accepted do throwError "unexpected recognition result for {body}"
      if let some coordinate := result then
        unless ← isDefEq coordinate body.getAppArgs[4]! do
          throwError "nonnegative recognition changed its coordinates"
      unless before.mvarCounter == (← getMCtx).mvarCounter &&
          before.lmvarCounter == (← getMCtx).lmvarCounter do
        throwError "nonnegative recognition changed caller metavariables"
      unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
        throwError "nonnegative recognition changed declarations"

private abbrev Reals := ℝ
private def hiddenMembership (x : ℝ) : Prop := x ∈ ℝ₊

run_cmd liftTermElabM do
  check (← `(fun x : ℝ => x ∈ ℝ₊)) true
  check (← `(fun x : Reals => x ∈ Morew.Conic.Cone.nonnegativeScalar.carrier)) true
  check (← `(fun x : ℝ => x ^ 2 ∈ ℝ₊)) true
  check (← `(fun n : Nat => fun x : Fin n → ℝ => x ∈ ℝ₊^n)) true 1
  check (← `(fun x : Fin 0 → ℝ => x ∈ ℝ₊^0)) true
  check (← `(fun x : ℝ => hiddenMembership x)) false
  check (← `(fun x : ℝ => 0 ≤ x)) false
  check (← `(fun x : ℝ => x ∈ ({0} : Set ℝ))) false
  check (← `(fun x : ℝ =>
    @Membership.mem ℝ (ConvexCone ℝ ℝ) ⟨fun _ _ => True⟩ ℝ₊ x)) false
  check (← `(fun x : Fin 0 → ℝ =>
    @Membership.mem (Fin 0 → ℝ) (ConvexCone ℝ (Fin 0 → ℝ))
      ⟨fun _ _ => True⟩ ℝ₊^0 x)) false
  check (← `(fun x : ℝ =>
    (fun _ : Fin (if x ≤ 0 then 1 else 2) => x) ∈ ℝ₊^(if x ≤ 0 then 1 else 2))) false

-- Unresolved coordinates and instances hidden in local lets must be rejected
-- without assigning the caller's metavariable, even when unification could solve it.
run_cmd liftTermElabM do
  let source ← MorewTest.Affine.elaborate (← `(fun x : ℝ => x ∈ ℝ₊))
  lambdaTelescope source fun points body => do
    let args := body.getAppArgs
    for position in #[2, 4] do
      let type ← inferType args[position]!
      let hole ← mkFreshExprMVar type
      withLetDecl `hidden type hole fun binding => do
        let before ← getMCtx
        let environment ← getEnv
        let predicate := mkAppN body.getAppFn (args.set! position binding)
        unless (← Elab.Conic.nonnegativeValue? points[0]! predicate).isNone do
          throwError "unresolved nonnegative membership was accepted"
        if ← hole.mvarId!.isAssigned then throwError "recognition assigned a caller metavariable"
        unless before.mvarCounter == (← getMCtx).mvarCounter &&
            before.lmvarCounter == (← getMCtx).lmvarCounter do
          throwError "failed recognition changed caller metavariables"
        unless MorewTest.sameLocalDeclarationNames environment (← getEnv) do
          throwError "failed recognition changed declarations"

end MorewTest.Conic.Nonnegative
