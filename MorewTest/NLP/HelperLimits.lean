/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.NLP.HelperFixtures
import MorewTest.NLP.DomainSupport
import MorewTest.Environment
import Morew.Elab.Affine

/-!
# Shared smooth helper budgets and atomic failures

Limits apply across sibling helper expansions and to substitutions exposed by
helpers. Native recognition remains available with any expansion budget disabled.
-/

namespace MorewTest.NLP.HelperLimits

open Lean Lean.Meta Lean.Elab.Term
open MorewTest.NLP.Smooth MorewTest.NLP.HelperFixtures

private def unchanged (before : MetavarContext) (environment : Environment) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.depth == after.depth do
    throwError "helper certification leaked scratch metavariables"
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "helper certification changed an existing assignment"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "helper certification assigned a caller hole"
  if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
    throwError "helper certification leaked declaration {name}"

private def assertLimit (term : TSyntax `term) (option : String)
    (helper : String) (limit : Nat) (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let before ← getMCtx
    let environment ← getEnv
    let result ← Morew.Elab.NLP.Smooth.certifyGlobal source
    unchanged before environment
    let .error error := result | throwError "smooth helper expansion exceeded {option}"
    unless error.kind == .expansionLimit && error.source == source do
      throwError "expected a structured helper limit failure: {error.reason}"
    let message ← error.reason.toString
    unless message.contains option && message.contains helper &&
        message.contains s!"limit {limit}" do
      throwError "helper limit diagnostic omitted its option, helper, or configured limit: {message}"

set_option morew.smooth.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => x * x + Real.exp x))
  assertRejected (← `(fun x : ℝ => square x)) .unknownHead

set_option morew.smooth.maxExpansionSteps 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => x * x + Real.exp x))
  assertRejected (← `(fun x : ℝ => square x)) .unknownHead

set_option morew.smooth.maxExpansionNodes 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => x * x + Real.exp x))
  assertRejected (← `(fun x : ℝ => square x)) .unknownHead

set_option morew.smooth.maxExpansionDepth 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => square x))
  assertLimit (← `(fun x : ℝ => nestedSquare x)) "morew.smooth.maxExpansionDepth" "square" 1
  assertLimit (← `(fun x : ℝ => (selectedHelper x).1)) "morew.smooth.maxExpansionDepth" "square" 1
  assertLimit (← `(fun x : ℝ => (partialAddPair x).1 x)) "morew.smooth.maxExpansionDepth" "square" 1

set_option morew.smooth.maxExpansionDepth 2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => nestedSquare x))
  assertSmooth (← `(fun x : ℝ => (selectedHelper x).1))
  assertSmooth (← `(fun x : ℝ => (partialAddPair x).1 x))

set_option morew.smooth.maxExpansionSteps 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => square x))
  assertLimit (← `(fun x : ℝ => square x + square x)) "morew.smooth.maxExpansionSteps" "square" 1
  assertSmooth (← `(fun x : ℝ => square x))
  Domain.assertDomain (← `(fun c : ℝ => ((fun _x : ℝ => True),
    #[fun x : ℝ => withEvidence c x]))) 1
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => square x, fun x : ℝ => square x])))
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => Real.log (coefficient x)])))
  Domain.assertDomain (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => Real.log (square x + 1)])))

set_option morew.smooth.maxExpansionSteps 2 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => square x + square x))

set_option morew.smooth.maxExpansionNodes 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun x : ℝ => square x)) "morew.smooth.maxExpansionNodes" "square" 1
  assertSmooth (← `(fun x : ℝ =>
    ((fun y : ℝ => y + y + y + y), (0 : ℝ)).1
      (x + x + x + x + x + x + x + x)))
  assertSmooth (← `(fun c : ℝ => fun x : ℝ =>
    let y := c + c + c + c + c + c + c + c
    let z := y + y + y + y
    (z + z + z + z) * x)) 1

-- All inputs fit the limit; helper substitution creates the oversized tree.
set_option morew.smooth.maxExpansionNodes 200 in
run_cmd Lean.Elab.Command.liftTermElabM do
  for (term, helper) in #[
      ((← `(fun x : ℝ => duplicate (x + x + x + x + x + x + x + x))), "duplicate"),
      ((← `(fun x : ℝ => duplicateLet x)), "duplicateLet"),
      ((← `(fun x : ℝ => applyHelper (fun y => y + y + y + y)
        (x + x + x + x + x + x + x + x))), "applyHelper"),
      ((← `(fun x : ℝ => projectedDuplicate.1
        (x + x + x + x + x + x + x + x))), "projectedDuplicate"),
      ((← `(fun x : ℝ => aliasDuplicate x)), "aliasDuplicate")] do
    unless (← elaborate term).sizeWithoutSharing < 200 do
      throwError "growth regression no longer starts below its node budget"
    assertLimit term "morew.smooth.maxExpansionNodes" helper 200
  assertLimit (← `(fun c : ℝ => fun x : ℝ => duplicateIndependentLet c x))
    "morew.smooth.maxExpansionNodes" "duplicateIndependentLet" 200 1
  assertLimit (← `(fun c : ℝ => fun x : ℝ =>
    let y := c + c + c + c + c + c + c + c
    repeatCoefficient y x))
    "morew.smooth.maxExpansionNodes" "repeatCoefficient" 200 1
  assertLimit (← `(fun c : ℝ => fun x : ℝ =>
    let y := c + c + c + c + c + c + c + c
    let p := (y, (0 : ℝ))
    repeatCoefficient p.1 x))
    "morew.smooth.maxExpansionNodes" "repeatCoefficient" 200 1
  assertLimit (← `(fun c : ℝ => fun x : Fin 2 → ℝ =>
    let y := c + c + c + c + c + c + c + c
    ∑ i, let p := (y, i)
         repeatCoefficient p.1 (x i)))
    "morew.smooth.maxExpansionNodes" "repeatCoefficient" 200 1

-- Closing the inner binding multiplies the outer binding's occurrences.
-- Charging only each original let body would fit this limit incorrectly.
set_option morew.smooth.maxExpansionNodes 1500 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertLimit (← `(fun c : ℝ => fun x : ℝ => chainedIndependentLets c x))
    "morew.smooth.maxExpansionNodes" "chainedIndependentLets" 1500 1
  assertLimit (← `(fun c : ℝ => fun x : ℝ =>
    let y := c + c + c + c + c + c + c + c
    let z := y + y + y + y
    repeatCoefficient z x))
    "morew.smooth.maxExpansionNodes" "repeatCoefficient" 1500 1

set_option morew.smooth.maxExpansionNodes 10000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => duplicate (x + x + x + x + x + x + x + x)))
  assertSmooth (← `(fun x : ℝ => duplicateLet x))
  assertSmooth (← `(fun x : ℝ => applyHelper (fun y => y + y + y + y)
    (x + x + x + x + x + x + x + x)))
  assertSmooth (← `(fun x : ℝ => projectedDuplicate.1
    (x + x + x + x + x + x + x + x)))
  assertSmooth (← `(fun x : ℝ => aliasDuplicate x))
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => duplicateIndependentLet c x)) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => chainedIndependentLets c x)) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ =>
    let y := c + c + c + c + c + c + c + c
    let z := y + y + y + y
    repeatCoefficient z x)) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ =>
    let y := c + c + c + c + c + c + c + c
    let p := (y, (0 : ℝ))
    repeatCoefficient p.1 x)) 1
  assertSmooth (← `(fun c : ℝ => fun x : Fin 2 → ℝ =>
    let y := c + c + c + c + c + c + c + c
    ∑ i, let p := (y, i)
         repeatCoefficient p.1 (x i))) 1
  Domain.assertDomain (← `(fun c : ℝ => ((fun _x : ℝ => True),
    #[fun x : ℝ => chainedIndependentLets c x]))) 1

-- Cache hits still consume the cumulative node budget for every occurrence.
set_option morew.smooth.maxExpansionNodes 32 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => square x))
  assertLimit (← `(fun x : ℝ => square x + square x))
    "morew.smooth.maxExpansionNodes" "square" 32
  assertSmooth (← `(fun x : ℝ => square x))
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => square x +
    (let y := c + c + c + c + c + c + c + c
     let z := y + y + y + y
     (z + z + z + z) * x))) 1
  assertSmooth (← `(fun c : ℝ => fun x : ℝ =>
    let y := c + c + c + c + c + c + c + c
    let z := y + y + y + y
    square x + (z + z + z + z) * x)) 1

-- Local options restore on leaving their command and do not cross certifiers.
set_option morew.affine.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => nestedSquare x))
  let source ← elaborate (← `(fun x : ℝ => shift x))
  let .error _ ← Morew.Elab.Affine.reifyAffine source
    | throwError "affine expansion unexpectedly ignored its disabled option"

set_option morew.smooth.maxExpansionDepth 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  assertRejected (← `(fun x : ℝ => square x)) .unknownHead
  let source ← elaborate (← `(fun x : ℝ => shift x))
  let .ok result ← Morew.Elab.Affine.reifyAffine source
    | throwError "smooth options disabled affine helper expansion"
  checkWithKernel result.map
  checkWithKernel result.pointwiseEquality

run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun x : ℝ => nestedSquare x))
  let source ← elaborate (← `(fun x : ℝ => shift x))
  let .ok result ← Morew.Elab.Affine.reifyAffine source
    | throwError "a local expansion option escaped its command"
  checkWithKernel result.map
  checkWithKernel result.pointwiseEquality

-- Successful expansion and failures preserve unrelated caller state alike.
run_cmd Lean.Elab.Command.liftTermElabM do
  let good ← elaborate (← `(fun x : ℝ => nestedSquare x))
  let bad ← elaborate (← `(fun x : ℝ => square x + nestedLog x))
  let hole ← mkFreshExprMVar (mkConst ``Nat)
  let assigned ← mkFreshExprMVar (mkConst ``Nat)
  assigned.mvarId!.assign (mkNatLit 17)
  for source in #[good, bad] do
    let before ← getMCtx
    let environment ← getEnv
    let result ← Morew.Elab.NLP.Smooth.certifyGlobal source
    unchanged before environment
    match result with
    | .ok proof =>
      unless source == good do throwError "restricted helper unexpectedly certified"
      checkCertificate source proof
    | .error error =>
      unless source == bad && error.kind == .restrictedDomain do
        throwError "unexpected helper certification failure: {error.reason}"
  if ← hole.mvarId!.isAssigned then throwError "helper certification filled a caller hole"
  unless (← instantiateMVars assigned) == mkNatLit 17 do
    throwError "helper certification lost an existing assignment"

-- Expansion cannot erase an unresolved argument before input validation.
run_cmd Lean.Elab.Command.liftTermElabM do
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => ignored c + square x))
  let missing ← mkFreshExprMVar (mkConst ``Real)
  withLetDecl `coefficient (mkConst ``Real) missing fun coefficient => do
    let source := mkApp builder coefficient
    let before ← getMCtx
    let environment ← getEnv
    let result ← Morew.Elab.NLP.Smooth.certifyGlobal source
    unchanged before environment
    let .error error := result | throwError "helper expansion erased an incomplete argument"
    unless error.kind == .unresolved && error.source == source do
      throwError "helper expansion changed the unresolved-input boundary"

-- This dependent helper would erase its entire argument once expanded. Input
-- validation must inspect the original local alias before that can happen.
run_cmd Lean.Elab.Command.liftTermElabM do
  assertSmooth (← `(fun c : ℝ => fun x : ℝ => ignored (c + x))) 1
  let builder ← elaborate (← `(fun c : ℝ => fun x : ℝ => ignored (c + x)))
  let missing ← mkFreshExprMVar (mkConst ``Real)
  withLetDecl `coefficient (mkConst ``Real) missing fun coefficient => do
    let source := mkApp builder coefficient
    if source.hasMVar then
      throwError "ignored-argument hole is not hidden in its local alias"
    let before ← getMCtx
    let environment ← getEnv
    let result ← Morew.Elab.NLP.Smooth.certifyGlobal source
    unchanged before environment
    let .error error := result
      | throwError "dependent helper expansion erased an incomplete argument"
    unless error.kind == .unresolved && error.source == source do
      throwError "dependent helper expansion changed the unresolved-input boundary"
  if ← missing.mvarId!.isAssigned then
    throwError "ignored-argument validation filled a caller hole"

set_option morew.smooth.maxExpansionSteps 1 in
run_cmd Lean.Elab.Command.liftTermElabM do
  Domain.assertDomainRejected (← `(((fun _x : ℝ => True),
    #[fun x : ℝ => square x + square x]))) .expansionLimit

end MorewTest.NLP.HelperLimits
