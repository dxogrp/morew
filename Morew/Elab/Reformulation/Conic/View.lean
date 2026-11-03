/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.View
import Morew.Elab.Reformulation.Conic.PowerChain
import Morew.Conic.SecondOrder
import Morew.Conic.Exponential.Cone
import Morew.Conic.PSD

/-!
# Conic reformulation presentation

Import-installed cone notation, checked replay templates, and mathematical print
recipes. The shared presentation machinery does not depend on this module.
-/

namespace Morew.Elab.Reformulation.Conic

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

-- Exact syntax can share a power cone's proof without enabling readable cone
-- notation. This internal flag is also kept separate from ordinary printing.
private def powerMembershipReplayOption : Name :=
  `Morew.Elab.Reformulation.powerMembershipReplay

-- PSD coordinates use a proof-bearing symmetric subtype internally. Only the
-- compact print payload may abbreviate its conversion to the ordinary matrix.
private def compactPSDOption : Name :=
  `Morew.Elab.Reformulation.compactPSD

-- Enabled only inside the coordinates of a checked PSD membership. Nested
-- block matrices may omit conversions without affecting unrelated terms.
private def compactPSDCoordinatesOption : Name :=
  `Morew.Elab.Reformulation.compactPSDCoordinates

-- Applied Lp coordinate projections are implicit in ordinary function notation.
-- Enable this only for print payloads; reconstruction views retain the fields.
private def coordinateNotationOption : Name :=
  `Morew.Elab.Reformulation.coordinateNotation

-- Matrix literals infer dimensions as successor constructors. Render just
-- these literal constructors as numerals, retaining symbolic dimensions.
private partial def psdDimensionLiteral? (dimension : Expr) : MetaM (Option Nat) := do
  let dimension := dimension.consumeMData
  if dimension.isConstOf ``Nat.zero then return some 0
  if dimension.isAppOfArity ``Nat.succ 1 then
    return (← psdDimensionLiteral? dimension.getAppArgs[0]!).map (· + 1)
  let some n ← getNatValue? dimension | return none
  -- `getNatValue?` reads the numeral index without checking its `OfNat`
  -- instance. A custom instance can give that same index a different value.
  if ← isDefEq dimension (mkNatLit n) then return some n
  return none

-- Ordinary display syntax can be reconstructed. A freshly written numeral
-- must therefore select an instance with the same value in its current context.
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
  if cone.isConstOf ``Morew.Conic.Cone.nonnegativeScalar then
    return ← `(ℝ₊)
  guard <| cone.isAppOfArity ``Morew.Conic.Cone.secondOrder 1 ||
    cone.isAppOfArity ``Morew.Conic.Cone.rotatedSecondOrder 1 ||
    cone.isAppOfArity ``Morew.Conic.Cone.nonnegative 1 ||
    cone.isAppOfArity ``Morew.Conic.Cone.positiveSemidefinite 1
  -- Keep the original subexpression position, so dimension references are
  -- frozen by the same pass as the rest of the generated presentation.
  let dimension ← withAppArg <| withAppArg do
    -- Exact replay retains the original numeral instances and constructors.
    if cone.isAppOfArity ``Morew.Conic.Cone.positiveSemidefinite 1 &&
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
  else if cone.isAppOfArity ``Morew.Conic.Cone.positiveSemidefinite 1 then
    `(PSD $dimension)
  else
    `(ℝ₊^$dimension)

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.WithLp.ofLp]
private def delabLpCoordinate : Delab := do
  let options ← getOptions
  unless options.getBool coordinateNotationOption && !options.getBool `pp.explicit do failure
  withOverApp 4 do
    let expression ← getExpr
    guard <| expression.isAppOfArity ``WithLp.ofLp 4
    let args := expression.getAppArgs
    let domain ← inferType args[2]!
    let functionType := Lean.mkLambda `_ .default domain args[1]!
    let projection := mkAppN expression.getAppFn (args.extract 0 2)
    let canonical ← mkAppOptM ``CoeFun.mk
      #[some domain, some functionType, some projection]
    guard (← presentationInstanceResynthesizes canonical)
    let value ← withNaryArg 2 delab
    let index ← withNaryArg 3 delab
    `($value $index)

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

-- Preserve the exact bundled cone and proof once, rather than repeating them
-- in dependent coordinate and membership-instance arguments. Replaying the
-- closed lambda template leaves ordinary structural beta reduction available
-- to later commands, without introducing an opaque predicate helper.
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

-- The bundled cone and the raw set use different membership instances. Rewrite
-- only the complete readable proposition; exact replay retains the cone proof.
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
  -- The shared stored-instance renderer preceded this renderer before the
  -- module split. Preserve that precedence independently of registration order.
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
    -- Protect just the canonical set-membership instance. Making the whole
    -- bundled proposition explicit also exposes arithmetic proofs, which the
    -- readable printer can omit and thereby make impossible to replay.
    return ← `(@Membership.mem _ _ $(mkCIdent ``Set.instMembership) (POW $exponent) $value)
  `($value ∈ POW $exponent)

private def presentationSingletonMembership {Y : Type} (value zero : Y) : Prop :=
  value ∈ ({zero} : Set Y)

-- A readable singleton needs its container type when the stored view is
-- elaborated again: `value ∈ {0}` alone leaves Set versus Finset ambiguous.
-- Replay syntax already keeps explicit instances; only annotate the readable
-- canonical set spelling, preserving both subexpression positions and values.
open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Membership.mem]
private def delabZeroConeMembership : Delab := do
  unless (← getOptions).getBool presentationNotationOption &&
      !(← getOptions).getBool `pp.explicit do failure
  let expression ← getExpr
  guard <| expression.isAppOfArity ``Membership.mem 5
  let args := expression.getAppArgs
  guard <| (← whnfUntil args[1]! ``Set).isSome
  let target ← whnf args[0]!
  unless target.isConstOf ``Real do
    let .forallE _ index range _ := target | failure
    let range ← whnf range
    guard <| !range.hasLooseBVars && range.isConstOf ``Real &&
      (← whnf index).isAppOfArity ``Fin 1
  let singleton := args[3]!.consumeMData
  guard <| singleton.isAppOfArity ``Singleton.singleton 4
  let singletonArgs := singleton.getAppArgs
  let zero := singletonArgs[3]!.consumeMData
  guard <| zero.isAppOfArity ``Zero.zero 2 ||
    (zero.isAppOfArity ``OfNat.ofNat 3 &&
      (zero.getAppArgs[1]! == mkRawNatLit 0 || zero.getAppArgs[1]! == mkNatLit 0))
  let template ← mkAppM ``presentationSingletonMembership #[args[4]!, zero]
  let some template ← unfoldDefinition? template | failure
  let canonical := template.getAppArgs
  guard (← isDefEq args[2]! canonical[2]!)
  guard (← isDefEq singletonArgs[2]! canonical[3]!.getAppArgs[2]!)
  let zeroInstance := zero.getAppArgs[if zero.isAppOfArity ``Zero.zero 2 then 1 else 2]!
  unless (← presentationInstanceResynthesizes args[2]!) &&
      (← presentationInstanceResynthesizes singletonArgs[2]!) &&
      (← presentationInstanceResynthesizes zeroInstance) do
    return ← withOptions (fun options => options.setBool `pp.explicit true
      |>.setBool `pp.instances true) delabApp
  let value ← withNaryArg 4 delab
  let set ← withNaryArg 3 delab
  let type ← withNaryArg 1 delab
  `($value ∈ ($set : $type))

private def presentationPSDMembership (n : Nat)
    (value : Morew.Conic.SymmetricMatrix n) : Prop :=
  value ∈ (Morew.Conic.Cone.positiveSemidefinite n).carrier

open Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr in
@[delab app.Morew.Conic.SymmetricMatrix.ofMatrix]
private def delabCompactPSDCoordinate : Delab := do
  let options ← getOptions
  unless options.getBool compactPSDCoordinatesOption && options.getBool compactPSDOption &&
      options.getBool presentationNotationOption && !options.getBool `pp.explicit &&
      !getPPProofs options do failure
  guard <| (← getExpr).isAppOfArity ``Morew.Conic.SymmetricMatrix.ofMatrix 3
  withNaryArg 1 delab

-- Constant diagonals have no meaningful index name. Rename only the unused
-- binder in this display copy, retaining the normal application delaborator.
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

-- This mathematical display deliberately omits symmetric-subtype conversions,
-- including those nested inside block matrices in the PSD coordinates.
-- Ordinary display syntax, detailed printing, and exact replay retain them.
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
  guard <| cone.isAppOfArity ``Morew.Conic.Cone.positiveSemidefinite 1
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
    | .compact => options.setBool compactPSDOption true |>.setBool coordinateNotationOption true
    | .detailed => options.setBool coordinateNotationOption true
  prepareReadable expression := do
    -- Exact cone replay shares the range proof through a closed lambda.
    -- Readable presentations expose its resulting membership directly.
    if expression.isApp && expression.getAppFn.isLambda &&
        (expression.getAppFn.find? (·.isConstOf ``presentationPowerMembershipInstance)).isSome then
      return some expression.headBeta
    return none
  mathematicalRows := powerChainPrintRows

end Morew.Elab.Reformulation.Conic
