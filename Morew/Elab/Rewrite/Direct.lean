/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Checked reduction for direct certification

A surface reduction may expose a directly certifiable function or predicate.
Failed reductions retain the original operation instances for rule discovery.
-/

namespace Morew.Elab.Rewrite.Direct

open Lean Lean.Meta

/-- Retain a definitionally equal reduction only after complete direct checking.
The reducer and certifier cannot change caller metavariables on failure. -/
def normalize (expression : Expr) (reduce : Expr → MetaM Expr)
    (certify : Expr → MetaM Bool) : MetaM Expr := do
  let checked : Except Unit Expr ← State.withIsolatedMVars do
    try
      let candidate ← reduce expression
      if candidate == expression then return .ok expression
      unless ← isDefEq candidate expression do return .error ()
      unless ← certify candidate do return .error ()
      return .ok candidate
    catch _ => return .error ()
  return checked.toOption.getD expression

private partial def normalizeBody (point body : Expr) (reduce : Expr → MetaM Expr)
    (certify : Expr → MetaM Bool) (opaqueProblemDependencies : Bool)
    (bindings : Array Expr := #[]) : MetaM Expr := do
  let body ← Expr.reduceStructure body (preserveLets := true)
    (opaqueProblemDependencies? := if opaqueProblemDependencies then some point else none)
  if let .letE name type value rest nondep := body then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← normalizeBody point (rest.instantiate1 binding) reduce certify
        opaqueProblemDependencies (bindings.push binding)
      mkLetFVars #[binding] result
        (usedLetOnly := false) (generalizeNondepLet := false)
  if body.isAppOfArity ``And 2 then
    return mkApp2 (mkConst ``And)
      (← normalizeBody point body.getAppArgs[0]! reduce certify opaqueProblemDependencies bindings)
      (← normalizeBody point body.getAppArgs[1]! reduce certify opaqueProblemDependencies bindings)
  normalize body reduce fun candidate => do
    let scopedBody ← mkLetFVars bindings candidate
      (usedLetOnly := false) (generalizeNondepLet := false)
    certify (← mkLambdaFVars #[point] scopedBody)

/-- Check conjunction leaves independently, retaining their original grouping
and scoped proof lets. An unsuccessful leaf stays unchanged for exact matching. -/
def normalizePredicate (predicate : Expr) (reduce : Expr → MetaM Expr)
    (certify : Expr → MetaM Bool) (opaqueProblemDependencies : Bool := false) : MetaM Expr := do
  let .forallE _ domain _ _ ← whnf (← inferType predicate)
    | throwError "expected a predicate for direct normalization"
  withLocalDeclD `point domain fun point => do
    mkLambdaFVars #[point] (← normalizeBody point (mkApp predicate point) reduce certify
      opaqueProblemDependencies)

end Morew.Elab.Rewrite.Direct
