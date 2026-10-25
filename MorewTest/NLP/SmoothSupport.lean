/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Smooth
import Lean.Meta.Check

/-!
# Assertions for global smoothness certificates

Every success is checked by the kernel against the original function on the
whole domain. Rejections inspect the structured diagnostic, rather than merely
checking that some elaboration failed.
-/

namespace MorewTest.NLP.Smooth

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.NLP.Smooth

def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasSorry || expression.hasMVar then
    throwError "smoothness test did not fully elaborate: {expression}"
  return expression

def checkCertificate (source proof : Expr) : MetaM Unit := do
  if proof.hasSorry || proof.hasMVar then
    throwError "smoothness certification returned an incomplete proof"
  withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
    checkWithKernel proof
  let proofType ← inferType proof
  unless proofType.isAppOfArity ``ContDiffOn 11 do
    throwError "smoothness certification proved a different predicate: {proofType}"
  let args := proofType.getAppArgs
  unless args[0]!.isConstOf ``Real && args[5]!.isConstOf ``Real do
    throwError "smoothness certificate changed the scalar field or result space"
  let two ← mkNumeral (← inferType args[8]!) 2
  let univ ← mkAppOptM ``Set.univ #[some args[2]!]
  let expected := mkAppN proofType.getAppFn
    (((args.set! 8 two).set! 9 source).set! 10 univ)
  unless ← isDefEq proofType expected do
    throwError "certificate does not prove C² smoothness of the original source on Set.univ"

def checkSuccess (source : Expr) : MetaM Expr := do
  match ← certifyGlobal source with
  | .ok proof =>
    checkCertificate source proof
    return proof
  | .error error =>
    throwError "expected global smoothness of {source}\n{error.reason}"

def checkFailure (source : Expr) (kind : SmoothFailureKind)
    (expectedHead? : Option Name := none) : MetaM Unit := do
  let .error error ← certifyGlobal source
    | throwError "unsupported smoothness source was certified: {source}"
  unless error.kind == kind do
    throwError "wrong smoothness failure kind for {source}: {repr error.kind}\n{error.reason}"
  unless error.source == source do
    throwError "smoothness failure lost the original source"
  if (← error.reason.toString).isEmpty then
    throwError "smoothness rejection has no explanation"
  if kind != .unresolved && (error.type.hasMVar || error.type.hasSorry) then
    throwError "smoothness rejection reports an incomplete operand type"
  if let some expectedHead := expectedHead? then
    unless error.expression.consumeMData.getAppFn.isConstOf expectedHead do
      throwError "smoothness rejection identifies the wrong operand: {error.expression}"
    unless ← isDefEq error.type (mkConst ``Real) do
      throwError "smoothness rejection reports the wrong scalar operand type"

def assertSmooth (term : TSyntax `term) (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source =>
    discard <| checkSuccess source

def assertRejected (term : TSyntax `term) (kind : SmoothFailureKind)
    (parameterCount : Nat := 0) (expectedHead? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source =>
    checkFailure source kind expectedHead?

end MorewTest.NLP.Smooth
