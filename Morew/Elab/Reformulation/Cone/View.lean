/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.View
import Morew.Elab.Reformulation.Cone.PowerChain
import Morew.Conic.SecondOrder
import Morew.Conic.Exponential.Cone
import Morew.Conic.PSD

/-! Conic notation and syntax for reconstructing and displaying constraints. -/

namespace Morew.Elab.Reformulation.Cone

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

-- Share power-cone proofs in exact syntax without readable notation.
private def powerMembershipReplayOption : Name :=
  `Morew.Elab.Reformulation.powerMembershipReplay

-- Abbreviate symmetric-subtype conversions only in compact printing.
private def compactPSDOption : Name :=
  `Morew.Elab.Reformulation.compactPSD

-- Allow nested matrix conversion shorthand only within certified PSD coordinates.
private def compactPSDCoordinatesOption : Name :=
  `Morew.Elab.Reformulation.compactPSDCoordinates

-- Render literal successor dimensions as numerals; retain symbolic dimensions.
private partial def psdDimensionLiteral? (dimension : Expr) : MetaM (Option Nat) := do
  let dimension := dimension.consumeMData
  if dimension.isConstOf ``Nat.zero then return some 0
  if dimension.isAppOfArity ``Nat.succ 1 then
    return (← psdDimensionLiteral? dimension.getAppArgs[0]!).map (· + 1)
  let some n ← getNatValue? dimension | return none
  -- Check `OfNat` instances before interpreting numeral indices.
  if ← isDefEq dimension (mkNatLit n) then return some n
  return none

-- Use numeral syntax only when its current instance has the same value.
private def psdDimensionNumeralResynthesizes (dimension : Expr) (n : Nat) : MetaM Bool :=
  withoutModifyingState do
    let type ← mkAppM ``OfNat #[mkConst ``Nat, mkNatLit n]
    match ← trySynthInstance type with
    | .some inferred =>
      let numeral ← mkAppOptM ``OfNat.ofNat
        #[some (mkConst ``Nat), some (mkNatLit n), some inferred]
      isDefEq dimension numeral
    | _ => pure false

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Morew.Conic.Cone.carrier]
private def delabConeCarrier : Delab := do
  unless (← getOptions).getBool presentationNotationOption do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``Morew.Conic.Cone.carrier 1
  let cone := expression.getAppArgs[0]!
  if cone.isConstOf ``Morew.Conic.Cone.exponential then
    return ← `(EXP)
  if cone.isConstOf ``Morew.Conic.Cone.nonnegScalar then
    return ← `(ℝ₊)
  guard <| cone.isAppOfArity ``Morew.Conic.Cone.secondOrder 1 ||
    cone.isAppOfArity ``Morew.Conic.Cone.rotatedSecondOrder 1 ||
    cone.isAppOfArity ``Morew.Conic.Cone.nonneg 1 ||
    cone.isAppOfArity ``Morew.Conic.Cone.psd 1
  -- Retain subexpression positions for fixed dimension references.
  let dimension ← withAppArg <| withAppArg do
    -- Syntax used to reconstruct expressions retains the original numeral instances and constructors.
    if cone.isAppOfArity ``Morew.Conic.Cone.psd 1 &&
        !(← getOptions).getBool `pp.explicit then
      if let some n ← psdDimensionLiteral? (← getExpr) then
        if (← getOptions).getBool compactPSDOption ||
            (← psdDimensionNumeralResynthesizes (← getExpr) n) then
          return ⟨Syntax.mkNumLit (toString n)⟩
    delab
  if cone.isAppOfArity ``Morew.Conic.Cone.secondOrder 1 then
    `(SOC $dimension)
  else if cone.isAppOfArity ``Morew.Conic.Cone.rotatedSecondOrder 1 then
    `(RSOC $dimension)
  else if cone.isAppOfArity ``Morew.Conic.Cone.psd 1 then
    `(PSD $dimension)
  else
    `(ℝ₊^$dimension)

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Morew.Conic.Cone.powerSet]
private def delabPowerSet : Delab := do
  unless (← getOptions).getBool presentationNotationOption do failure
  guard <| (← getExpr).isAppOfArity ``Morew.Conic.Cone.powerSet 1
  let exponent ← withAppArg delab
  `(POW $exponent)

private def presentationPowerMembership (α : ℝ) (hα : 0 < α ∧ α < 1)
    (value : ℝ × ℝ × ℝ) : Prop :=
  value ∈ ((Morew.Conic.Cone.power α hα).carrier : ConvexCone ℝ (ℝ × ℝ × ℝ))

@[instance_reducible]
private def presentationPowerMembershipInstance :
    Membership (ℝ × ℝ × ℝ) (ConvexCone ℝ (ℝ × ℝ × ℝ)) := inferInstance

private def presentationPowerSetMembership (α : ℝ) (value : ℝ × ℝ × ℝ) : Prop :=
  value ∈ Morew.Conic.Cone.powerSet α

-- Use a closed function to retain the cone and its proof when reconstructing expressions.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Membership.mem]
private def delabPowerConeReplay : Delab := do
  let options ← getOptions
  unless options.getBool `pp.explicit &&
      (options.getBool presentationNotationOption || options.getBool powerMembershipReplayOption) do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``Membership.mem 5
  let args := expression.getAppArgs
  let carrier := args[3]!.consumeMData
  guard <| carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1
  let cone := carrier.getAppArgs[0]!.consumeMData
  guard <| cone.isAppOfArity ``Morew.Conic.Cone.power 2
  let canonical := (mkAppN (← getConstInfo ``presentationPowerMembership).value!
    #[cone.getAppArgs[0]!, cone.getAppArgs[1]!, args[4]!]).headBeta
  guard (← isDefEq args[2]! canonical.getAppArgs[2]!)
  guard (← isDefEq expression canonical)
  let exponent ← withNaryArg 3 <| withAppArg <| withNaryArg 0 delab
  let evidence ← withNaryArg 3 <| withAppArg <| withNaryArg 1 delab
  let value ← withNaryArg 4 delab
  let function ← `(fun α hα value =>
    @Membership.mem _ _ $(mkCIdent ``presentationPowerMembershipInstance)
      ($(mkCIdent ``Morew.Conic.Cone.carrier) ($(mkCIdent ``Morew.Conic.Cone.power) α hα)) value)
  `($function $exponent $evidence $value)

-- Display membership in the defining set; retain cone proofs when reconstructing expressions.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Membership.mem]
private def delabPowerConeMembership : Delab := do
  unless (← getOptions).getBool presentationNotationOption &&
      !(← getOptions).getBool `pp.explicit do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``Membership.mem 5
  let args := expression.getAppArgs
  let carrier := args[3]!.consumeMData
  guard <| carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1
  let cone := carrier.getAppArgs[0]!.consumeMData
  guard <| cone.isAppOfArity ``Morew.Conic.Cone.power 2
  -- Give the stored-instance renderer precedence.
  unless ← presentationInstanceResynthesizes args[2]! do
    return ← withOptions (fun options => options.setBool `pp.explicit true
      |>.setBool `pp.instances true) delabApp
  let exponent := cone.getAppArgs[0]!
  let evidence := cone.getAppArgs[1]!
  let canonical := (mkAppN (← getConstInfo ``presentationPowerMembership).value!
    #[exponent, evidence, args[4]!]).headBeta
  guard (← isDefEq args[2]! canonical.getAppArgs[2]!)
  let asSet := (mkAppN (← getConstInfo ``presentationPowerSetMembership).value!
    #[exponent, args[4]!]).headBeta
  let value ← withNaryArg 4 delab
  let exponent ← withNaryArg 3 <| withAppArg <| withNaryArg 0 delab
  unless ← presentationInstanceResynthesizes asSet.getAppArgs[2]! do
    -- Make only canonical membership explicit; retain arithmetic syntax for reconstruction.
    return ← `(@Membership.mem _ _ $(mkCIdent ``Set.instMembership) (POW $exponent) $value)
  `($value ∈ POW $exponent)

private def presentationPSDMembership (n : Nat)
    (value : Morew.Conic.SymmetricMatrix n) : Prop :=
  value ∈ (Morew.Conic.Cone.psd n).carrier

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Morew.Conic.SymmetricMatrix.ofMatrix]
private def delabCompactPSDCoordinate : Delab := do
  let options ← getOptions
  unless options.getBool compactPSDCoordinatesOption && options.getBool compactPSDOption &&
      options.getBool presentationNotationOption && !options.getBool `pp.explicit &&
      !getPPProofs options do failure
  guard <| (← getExpr).isAppOfArity ``Morew.Conic.SymmetricMatrix.ofMatrix 3
  withNaryArg 1 delab

-- Rename unused constant-diagonal binders in the display copy.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Matrix.diagonal]
private def delabCompactConstantDiagonal : Delab := do
  let options ← getOptions
  unless options.getBool compactPSDOption && options.getBool presentationNotationOption &&
      !options.getBool `pp.explicit && !getPPProofs options do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``Matrix.diagonal 5
  let .lam _ domain body binderInfo := expression.getAppArgs[4]! | failure
  guard <| !body.hasLooseBVar 0
  let expression := mkApp expression.appFn! (.lam `_ domain body binderInfo)
  withTheReader SubExpr (fun context => { context with expr := expression }) delabApp

-- Omit symmetric-subtype conversions only in compact PSD printing.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Membership.mem]
private def delabCompactPSDMembership : Delab := do
  let options ← getOptions
  unless options.getBool compactPSDOption && options.getBool presentationNotationOption &&
      !options.getBool `pp.explicit && !getPPProofs options do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``Membership.mem 5
  let args := expression.getAppArgs
  let carrier := args[3]!.consumeMData
  guard <| carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1
  let cone := carrier.getAppArgs[0]!.consumeMData
  guard <| cone.isAppOfArity ``Morew.Conic.Cone.psd 1
  let canonical := (mkAppN (← getConstInfo ``presentationPSDMembership).value!
    #[cone.getAppArgs[0]!, args[4]!]).headBeta
  guard (← isDefEq args[2]! canonical.getAppArgs[2]!)
  guard (← isDefEq expression canonical)
  let matrix ← withOptions (·.setBool compactPSDCoordinatesOption true) <| withNaryArg 4 delab
  let cone ← withNaryArg 3 delab
  `($matrix ∈ $cone)

/-- Presentation support installed by the conic command entry point. -/
@[morew_reformulation_view presentation]
def viewHooks : Morew.Elab.Reformulation.ViewHooks where
  options mode options := match mode with
    | .exact => options.setBool powerMembershipReplayOption true
    | .compact => options.setBool compactPSDOption true
    | .detailed => options
  prepareReadable expression := do
    -- Display the membership relation defined by the stored function.
    if expression.isApp && expression.getAppFn.isLambda &&
        (expression.getAppFn.find? (·.isConstOf ``presentationPowerMembershipInstance)).isSome then
      return some expression.headBeta
    return none
  mathematicalRows := powerChainPrintRows

end Morew.Elab.Reformulation.Cone
