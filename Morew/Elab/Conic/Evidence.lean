/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Expr
import Morew.Elab.State
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.NormNum
import Lean.Meta.Check

/-!
# Independent conic parameter evidence

Exponent ranges use independent local hypotheses, their conjunction projections,
one supplied finite-index specialization, and bounded exact numeral/rational
evaluation. The `ofReal` bridge transports a checked real exponent greater than
one. This does not combine symbolic inequalities or obtain decision-dependent
premises from selected/generated rows.
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

private partial def projection? (proof goal : Expr) (index? : Option Expr) :
    MetaM (Option Expr) := do
  let type ← Expr.reduceStructure (← inferType proof)
  if ← isDefEq type goal then return some proof
  if type.isAppOfArity ``And 2 then
    if let some result ← projection? (← mkAppM ``And.left #[proof]) goal index? then
      return some result
    return ← projection? (← mkAppM ``And.right #[proof]) goal index?
  if let some index := index? then
    if let .forallE _ domain _ _ := type then
      if ← isDefEq domain (← inferType index) then
        return ← projection? (mkApp proof index) goal none
  return none

private theorem one_lt_toReal_ofReal {q : ℝ} (h : 1 < q) :
    1 < (ENNReal.ofReal q).toReal := by
  rw [ENNReal.toReal_ofReal (le_trans zero_le_one h.le)]
  exact h

/-- Normalize `ENNReal.toReal` of native numerals, inverses and divisions with
checked equalities. No contextual simp set or unfolding of named operands is used. -/
def normalizeToReal (expression : Expr) : MetaM Simp.Result := do
  let mut theorems : SimpTheorems := {}
  for declaration in #[``ENNReal.toReal_zero, ``ENNReal.toReal_one,
      ``ENNReal.toReal_ofNat, ``ENNReal.toReal_natCast, ``ENNReal.toReal_inv,
      ``ENNReal.toReal_div] do
    theorems ← theorems.addConst declaration
  let context ← Simp.mkContext (config := { zeta := false })
    (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
  return (← simp expression context).1

private partial def proveCore? (point goal : Expr) (index? : Option Expr) :
    MetaM (Option Expr) := do
  if (← Expr.depends point goal) || (← Expr.hasUnresolved goal) ||
      (← hasPlaceholders goal) then return none
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let proof := declaration.toExpr
    if (← Expr.depends point proof) || (← Expr.hasUnresolved proof) ||
        (← hasPlaceholders proof) then continue
    unless ← isProp declaration.type do continue
    if let some proof ← projection? proof goal index? then return some proof
  let goal ← Expr.reduceStructure goal
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    let some left ← proveCore? point args[0]! index? | return none
    let some right ← proveCore? point args[1]! index? | return none
    return some (← mkAppM ``And.intro #[left, right])
  unless goal.isAppOfArity ``LT.lt 4 || goal.isAppOfArity ``LE.le 4 do return none
  let args := goal.getAppArgs
  unless ← isDefEq args[0]! q(ℝ) do return none
  let left : Q(ℝ) := args[2]!
  let right : Q(ℝ) := args[3]!
  let canonical : Q(Prop) := if goal.isAppOfArity ``LT.lt 4 then q($left < $right)
    else q($left ≤ $right)
  unless ← isDefEq goal canonical do return none
  if goal.isAppOfArity ``LT.lt 4 && (← isDefEq left q((1 : ℝ))) &&
      right.isAppOfArity ``ENNReal.toReal 1 then
    let extended := right.getAppArgs[0]!
    if extended.isAppOfArity ``ENNReal.ofReal 1 then
      let real : Q(ℝ) := extended.getAppArgs[0]!
      if let some proof ← proveCore? point q(1 < $real) index? then
        return some (← mkAppM ``one_lt_toReal_ofReal #[proof])
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
        do
          let normalized ← normalizeToReal goal
          match ← Mathlib.Meta.NormNum.deriveBool normalized.expr with
          | ⟨true, proof⟩ => pure (some (← normalized.mkEqMPR proof))
          | _ => pure none
      match result with
      | some proof => pure proof
      | _ => throwError "independent parameter inequality was not established"
    return some proof
  catch _ => return none

/-- Produce checked parameter evidence without modifying caller metavariables.
Only exact hypotheses/conjunction projections, one supplied `Fin` index,
the checked `ofReal` bridge, and bounded numerical inequalities are available.
Decision-dependent and unresolved goals or indices return `none`. -/
def proveIndependent? (point goal : Expr) (index? : Option Expr := none) :
    MetaM (Option Expr) := do
  let result ← State.withIsolatedMVars do
    if let some index := index? then
      if (← Expr.depends point index) || (← Expr.hasUnresolved index) ||
          (← hasPlaceholders index) then return .error ()
      unless (← whnf (← inferType index)).isAppOfArity ``Fin 1 do return .error ()
    let some proof ← proveCore? point goal index? | return .error ()
    if (← Expr.depends point proof) || (← Expr.hasUnresolved proof) ||
        (← hasPlaceholders proof) then
      return .error ()
    unless ← isDefEq (← inferType proof) goal do return .error ()
    checkWithKernel proof
    return .ok proof
  return result.toOption

end Morew.Elab.Conic.Evidence
