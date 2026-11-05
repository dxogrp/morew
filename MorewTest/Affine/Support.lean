/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Affine
import Lean.Meta.Check
import MorewTest.ElabSupport

/-!
# Shared affine test assertions

Check generated maps against their source propositions and reject incomplete
certificates. Each behavior suite imports these helpers independently.
-/

namespace MorewTest.Affine

open Lean Lean.Meta Lean.Elab.Term
open Morew.Elab.Affine

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

end MorewTest.Affine
