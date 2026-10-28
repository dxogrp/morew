/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Expr
import Morew.Elab.State
import Mathlib.Tactic.NormNum
import Lean.Meta.Check

/-!
# Independent conic parameter evidence

Exponent ranges use independent local hypotheses, their conjunction projections,
and bounded exact numeral/rational evaluation. This does not combine symbolic
inequalities or obtain decision-dependent premises from selected/generated rows.
The same policy serves registered rules and direct parameterized-cone membership.
-/

namespace Morew.Elab.Conic.Evidence

open Lean Lean.Meta Qq

/-- Detect placeholders transitively through local types and values, including
proof lets that would otherwise hide a placeholder behind a free variable. -/
partial def hasPlaceholders (expression : Expr) (seen : FVarIdSet := {}) : MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasSorry then return true
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    unless seen.contains id do
      seen := seen.insert id
      let declaration ← id.getDecl
      if ← hasPlaceholders declaration.type seen then return true
      if let some value := declaration.value? (allowNondep := true) then
        if ← hasPlaceholders value seen then return true
  return false

private partial def projection? (proof goal : Expr) : MetaM (Option Expr) := do
  let type ← Expr.reduceStructure (← inferType proof)
  if ← isDefEq type goal then return some proof
  if type.isAppOfArity ``And 2 then
    if let some result ← projection? (← mkAppM ``And.left #[proof]) goal then
      return some result
    return ← projection? (← mkAppM ``And.right #[proof]) goal
  return none

private partial def proveCore? (point goal : Expr) : MetaM (Option Expr) := do
  if (← Expr.depends point goal) || (← Expr.hasUnresolved goal) ||
      (← hasPlaceholders goal) then return none
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let proof := declaration.toExpr
    if (← Expr.depends point proof) || (← Expr.hasUnresolved proof) ||
        (← hasPlaceholders proof) then continue
    unless ← isProp declaration.type do continue
    if let some proof ← projection? proof goal then return some proof
  let goal ← Expr.reduceStructure goal
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    let some left ← proveCore? point args[0]! | return none
    let some right ← proveCore? point args[1]! | return none
    return some (← mkAppM ``And.intro #[left, right])
  unless goal.isAppOfArity ``LT.lt 4 || goal.isAppOfArity ``LE.le 4 do return none
  let args := goal.getAppArgs
  unless ← isDefEq args[0]! q(ℝ) do return none
  let left : Q(ℝ) := args[2]!
  let right : Q(ℝ) := args[3]!
  let canonical : Q(Prop) := if goal.isAppOfArity ``LT.lt 4 then q($left < $right)
    else q($left ≤ $right)
  unless ← isDefEq goal canonical do return none
  let context ← readThe Core.Context
  let localLimit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
  let limit := if context.maxHeartbeats == 0 then localLimit else min context.maxHeartbeats localLimit
  try
    let proof ← mapLetDeclZeta `_parameterLE q(LE ℝ) q(inferInstance : LE ℝ) fun _ => do
      mapLetDeclZeta `_parameterLT q(LT ℝ) q(inferInstance : LT ℝ) fun _ => do
      mapLetDeclZeta `_parameterPreorder q(Preorder ℝ) q(inferInstance : Preorder ℝ) fun _ => do
      mapLetDeclZeta `_parameterPartialOrder q(PartialOrder ℝ)
        q(inferInstance : PartialOrder ℝ) fun _ => do
      let result ← withTheReader Core.Context
        (fun context => { context with maxHeartbeats := limit }) <|
        Mathlib.Meta.NormNum.deriveBool goal
      match result with
      | ⟨true, proof⟩ => pure proof
      | _ => throwError "independent parameter inequality was not established"
    return some proof
  catch _ => return none

/-- Produce checked parameter evidence without modifying caller metavariables.
Only exact hypotheses/conjunction projections and bounded numerical inequalities
are available. Decision-dependent and unresolved goals return `none`. -/
def proveIndependent? (point goal : Expr) : MetaM (Option Expr) := do
  let result ← State.withIsolatedMVars do
    let some proof ← proveCore? point goal | return .error ()
    if (← Expr.depends point proof) || (← Expr.hasUnresolved proof) ||
        (← hasPlaceholders proof) then
      return .error ()
    unless ← isDefEq (← inferType proof) goal do return .error ()
    checkWithKernel proof
    return .ok proof
  return result.toOption

end Morew.Elab.Conic.Evidence
