/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Domain
import MorewTest.NLP.SmoothSupport

/-!
# Assertions for inferred evaluation domains

Success checks every proof against the original predicate and source array.
Failure assertions inspect structured diagnostics after full term elaboration.
-/

namespace MorewTest.NLP.Domain

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.NLP.Domain Morew.Elab.NLP.Smooth

abbrev elaborate := MorewTest.NLP.Smooth.elaborate

def checkResult (feasible : Expr) (sources : Array Expr) (result : DomainResult) :
    MetaM Unit := do
  unless result.smooth.size == sources.size do
    throwError "domain certificate changed the number of supplied sources"
  if result.domain.hasMVar || result.domain.hasSorry then
    throwError "domain certification returned an incomplete domain"
  for proof in result.smooth ++ #[result.domainIsOpen, result.feasibleMemDomain] do
    if proof.hasSorry || proof.hasMVar then
      throwError "domain certification returned an incomplete proof"
    withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
      checkWithKernel proof
  let .forallE _ decision _ _ ← whnf (← inferType feasible)
    | throwError "domain test did not supply a predicate"
  let expectedOpen ← Morew.Elab.NLP.Space.withCanonicalSpaces #[decision] <|
    mkAppM ``IsOpen #[result.domain]
  unless ← isDefEq (← inferType result.domainIsOpen) expectedOpen do
    throwError "domain certificate proves openness of a different set"
  let expectedInclusion ← withLocalDeclD `point decision fun point => do
    let membership ← mkAppM ``Membership.mem #[result.domain, point]
    mkForallFVars #[point] (← mkArrow (mkApp feasible point) membership)
  unless ← isDefEq (← inferType result.feasibleMemDomain) expectedInclusion do
    throwError "domain certificate changed the original feasible predicate"
  for i in [:sources.size] do
    let proofType ← inferType result.smooth[i]!
    unless proofType.isAppOfArity ``ContDiffOn 11 do
      throwError "domain certificate proved a different predicate: {proofType}"
    let args := proofType.getAppArgs
    unless args[0]!.isConstOf ``Real && args[5]!.isConstOf ``Real do
      throwError "domain certificate changed the scalar field or result space"
    let two ← mkNumeral (← inferType args[8]!) 2
    let expected := mkAppN proofType.getAppFn
      (((args.set! 8 two).set! 9 sources[i]!).set! 10 result.domain)
    unless ← isDefEq proofType expected do
      throwError "domain certificate changed source {i} or its common domain"

def checkSuccess (feasible : Expr) (sources : Array Expr) : MetaM DomainResult := do
  match ← certify feasible sources with
  | .ok result =>
    checkResult feasible sources result
    return result
  | .error error =>
    throwError "expected domain certification of {sources} under {feasible}\n{error.reason}"

def checkFailure (feasible : Expr) (sources : Array Expr) (kind : SmoothFailureKind)
    (sourceIndex? : Option Nat := none) (rowIndex? : Option Nat := none)
    (expectedHead? : Option Name := none) : MetaM DomainError := do
  let .error error ← certify feasible sources
    | throwError "unsupported domain source or predicate was certified"
  unless error.kind == kind do
    throwError "wrong domain failure kind: {repr error.kind}, expected {repr kind}\n{error.reason}"
  unless error.sourceIndex? == sourceIndex? && error.rowIndex? == rowIndex? do
    throwError "domain failure lost its source or row position: {error.sourceIndex?}, {error.rowIndex?}"
  let original := sourceIndex?.map (sources[·]!) |>.getD feasible
  unless error.source == original do
    throwError "domain failure changed the original source"
  if (← error.reason.toString).isEmpty then
    throwError "domain rejection has no explanation"
  if kind != .unresolved && (error.type.hasMVar || error.type.hasSorry) then
    throwError "domain rejection reports an incomplete operand type"
  if kind == .feasibleInclusion && error.obligation?.isNone then
    throwError "domain inclusion failure omitted its exact obligation"
  if let some head := expectedHead? then
    unless error.expression.consumeMData.getAppFn.isConstOf head do
      throwError "domain rejection identifies the wrong operand: {error.expression}"
  return error

/-- Keep shared parameters in scope while extracting the literal source array. -/
def withInput (term : TSyntax `term) (parameterCount : Nat)
    (action : Expr → Array Expr → TermElabM Unit) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ input => do
    let input ← whnf input
    unless input.isAppOfArity ``Prod.mk 4 do
      throwError "expected a pair of a feasibility predicate and a literal source array"
    let args := input.getAppArgs
    let some sources ← getArrayLit? args[3]!
      | throwError "expected a literal array of source functions"
    action args[2]! sources

def assertDomain (term : TSyntax `term) (parameterCount : Nat := 0) : TermElabM Unit :=
  withInput term parameterCount fun feasible sources =>
    discard <| checkSuccess feasible sources

def assertDomainRejected (term : TSyntax `term) (kind : SmoothFailureKind)
    (parameterCount : Nat := 0) (sourceIndex? : Option Nat := some 0)
    (rowIndex? : Option Nat := none) (expectedHead? : Option Name := none) : TermElabM Unit :=
  withInput term parameterCount fun feasible sources =>
    discard <| checkFailure feasible sources kind sourceIndex? rowIndex? expectedHead?

end MorewTest.NLP.Domain
