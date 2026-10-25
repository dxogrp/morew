/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic
import Lean.Meta.Check

/-!
# Shared affine test assertions

Elaborate test inputs, check generated maps and rows against their exact source
propositions, and reject incomplete certificates. This module contains helpers
only, so each behavior suite can be compiled independently.
-/

namespace MorewTest.Affine

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Affine

def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasSorry || expression.hasMVar then
    throwError "affine test did not fully elaborate: {expression}"
  return expression

def checkResult (source : Expr) (result : AffineResult) : MetaM Unit := do
  for expression in #[result.map, result.pointwiseEquality] do
    if expression.hasMVar || expression.hasSorry then
      throwError "affine reification returned an incomplete certificate"
    withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
      checkWithKernel expression
  let .forallE _ domain _ _ ← whnf (← inferType source)
    | throwError "affine test source is not a function"
  let expected ← withLocalDeclD `x domain fun x => do
    let mapped := mkApp (← mkProjection result.map `toFun) x
    mkForallFVars #[x] (← mkEq mapped (source.beta #[x]))
  unless ← isDefEq (← inferType result.pointwiseEquality) expected do
    throwError "affine certificate proves the wrong statement"

def assertAffine (term : TSyntax `term) (parameterCount : Nat := 0)
    (provider : Morew.Elab.Affine.EvidenceProvider := {}) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    match ← reifyAffine source provider with
    | .ok result => checkResult source result
    | .error error =>
      throwError "expected affine recognition of {source}\n{error.reason}"

def assertRow (term : TSyntax `term) (parameterCount : Nat := 0) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    let result ← match ← Morew.Elab.Conic.normalizeRow source with
      | .ok result => pure result
      | .error error => throwError "expected affine row {source}\n{error.reason}"
    for expression in #[result.constraint, result.pointwiseIff] do
      if expression.hasMVar || expression.hasSorry then
        throwError "row normalization returned an incomplete certificate"
      checkWithKernel expression
    let constraintType ← whnf (← inferType result.constraint)
    unless constraintType.isAppOfArity ``Morew.Conic.Constraint 3 do
      throwError "normalization did not produce a semantic constraint"
    let .forallE _ domain _ _ ← whnf (← inferType source)
      | throwError "row test source is not a function"
    let expected ← withLocalDeclD `x domain fun x => do
      -- Reuse the row's explicit structures, so the test does not accidentally
      -- synthesize the unrelated ambient normed-space instances it is testing.
      let holds := mkAppN
        (mkConst ``Morew.Conic.Constraint.Holds constraintType.getAppFn.constLevels!)
        (constraintType.getAppArgs ++ #[result.constraint, x])
      mkForallFVars #[x] (← mkAppM ``Iff #[holds, source.beta #[x]])
    checkWithKernel expected
    unless ← isDefEq (← inferType result.pointwiseIff) expected do
      throwError "row certificate proves the wrong statement"

def assertUnsupported (term : TSyntax `term) (parameterCount : Nat := 0)
    (expectedHead? : Option Name := none) : TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    match ← reifyAffine source with
    | .ok _ => throwError "unexpected affine recognition of {source}"
    | .error error =>
      if (← error.reason.toString).isEmpty then
        throwError "unsupported expression has no failure reason"
      if let some expectedHead := expectedHead? then
        unless error.expression.consumeMData.getAppFn.isConstOf expectedHead do
          throwError "failure did not identify the unsupported subexpression"

def assertRowUnsupported (term : TSyntax `term) (parameterCount : Nat := 0) :
    TermElabM Unit := do
  let expression ← elaborate term
  lambdaBoundedTelescope expression parameterCount fun _ source => do
    match ← Morew.Elab.Conic.normalizeRow source with
    | .ok _ => throwError "unsupported row was accepted"
    | .error error =>
      if (← error.reason.toString).isEmpty then
        throwError "unsupported row was rejected without a reason"

end MorewTest.Affine
