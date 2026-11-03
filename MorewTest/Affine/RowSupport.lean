/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Affine.Support
import Morew.Elab.Conic

/-! Shared exact row-certificate assertions. -/

namespace MorewTest.Affine

open Lean Lean.Meta Lean.Elab.Term

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
      -- Reuse the row's explicit structures, independently of ambient instances.
      let holds := mkAppN
        (mkConst ``Morew.Conic.Constraint.Holds constraintType.getAppFn.constLevels!)
        (constraintType.getAppArgs ++ #[result.constraint, x])
      mkForallFVars #[x] (← mkAppM ``Iff #[holds, source.beta #[x]])
    checkWithKernel expected
    unless ← isDefEq (← inferType result.pointwiseIff) expected do
      throwError "row certificate proves the wrong statement"

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
