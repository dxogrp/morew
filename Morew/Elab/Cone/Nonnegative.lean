/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Cone
import Morew.Elab.Expr
import Morew.Elab.State

/-! Recognize scalar and finite-vector nonnegative-cone coordinates for sign evidence. -/

namespace Morew.Elab.Cone

open Lean Lean.Meta

private def canonicalNonnegativeMembership
    (cone : Morew.Conic.Cone) (value : cone.Space) : Prop :=
  value ∈ cone.carrier

/-- Recover nonnegative-cone coordinates after checking the membership instance. -/
def nonnegativeValue? (point body : Expr) : MetaM (Option Expr) := do
  let result : Except Unit Expr ← State.withIsolatedMVars do
    if !(body.isAppOfArity ``Membership.mem 5) || (← Expr.hasUnresolved body) then
      return .error ()
    let args := body.getAppArgs
    let carrier ← Expr.reduceStructure args[3]!
    let carrier := if carrier.isConstOf ``Morew.Conic.Cone.nonnegativeScalarCarrier then
        mkApp (mkConst ``Morew.Conic.Cone.carrier)
          (mkConst ``Morew.Conic.Cone.nonnegativeScalar)
      else carrier
    unless carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1 do return .error ()
    let cone ← Expr.reduceStructure carrier.getAppArgs[0]!
    unless cone.isConstOf ``Morew.Conic.Cone.nonnegativeScalar ||
        cone.isAppOfArity ``Morew.Conic.Cone.nonnegative 1 do return .error ()
    if ← Expr.depends point cone then return .error ()
    let value := args[4]!
    let template := (← getConstInfo ``canonicalNonnegativeMembership).value!
    let canonical := (mkAppN template #[cone, value]).headBeta
    unless ← isDefEq args[2]! canonical.getAppArgs[2]! do return .error ()
    unless ← isDefEq body canonical do return .error ()
    return .ok value
  return result.toOption

end Morew.Elab.Cone
