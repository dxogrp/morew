/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Polyhedral
import Morew.Elab.Atom
import Morew.Elab.Conic.Plan

/-!
# Checked plans for exact polyhedral constraint replacements

Native polyhedral recognition shares custom-rule adaptation and row certification
with the other conic planners.
-/

namespace Morew.Elab.Conic.Polyhedral

open Lean Lean.Meta
open Plan
open Morew.Elab.Rewrite.Plan

/-- A checked exact replacement, before presentation names are allocated. -/
abbrev Result := Plan.Result

/-- Independently selectable native rules. Norm carriers select disjoint variants. -/
inductive Rule where
  | absolute | positivePart | maximum | minimum | supremum | infimum | norm
  deriving BEq, Repr

/-- Stable order for exhaustive native-rule certification. -/
def rules : Array Rule :=
  #[.absolute, .positivePart, .maximum, .minimum, .supremum, .infimum, .norm]

private def realVectorDimension? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  let .forallE _ index body _ := type | return none
  if body.hasLooseBVars then return none
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 && (← whnf body).isConstOf ``Real do return none
  return some index.getAppArgs[0]!

private def representationProof (rule input bound : Expr) (hypograph : Bool := false) :
    MetaM Expr :=
  mkAppM (if hypograph then ``Morew.HypographRepresentation.source_iff_exists
    else ``Morew.EpigraphRepresentation.source_iff_exists) #[rule, input, bound]

private def theoremSides (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Iff 2 do throwError "internal error: expected an exact iff theorem"
  return (type.getAppArgs[0]!, type.getAppArgs[1]!)

-- Compare the operation instances themselves before checking the theorem's
-- full predicate. A custom operation that agrees only at these operands is
-- not evidence that the native rule applies.
private def sameOperationPrefix (actual expected : Expr) (operandCount : Nat) :
    MetaM Unit := do
  unless actual.getAppFn == expected.getAppFn &&
      actual.getAppNumArgs == expected.getAppNumArgs do
    throwError "unsupported native operation {actual}"
  let a := actual.getAppArgs
  let b := expected.getAppArgs
  for index in [:a.size - operandCount] do
    unless ← isDefEq a[index]! b[index]! do
      throwError "unsupported instance in native operation {actual}"

private def finiteExtremumProof (point operation bound : Expr) (minimum : Bool) :
    MetaM Expr := do
  let args := operation.getAppArgs
  unless args.size == 6 do throwError "unsupported finite extremum {operation}"
  if ← Affine.depends point args[3]! then
    throwError "the finite extremum's index set depends on a decision variable"
  let ruleName := if minimum then ``Morew.Rewrite.finsetInfHypograph
    else ``Morew.Rewrite.finsetSupEpigraph
  let rule ← mkAppM ruleName #[args[3]!, args[4]!]
  let proof ← representationProof rule args[5]! bound minimum
  let (lhs, _) ← theoremSides proof
  let expected ← Affine.reduceStructure lhs.getAppArgs[if minimum then 3 else 2]!
  sameOperationPrefix operation expected 3
  return proof

private def normProof (operation bound : Expr) : MetaM Expr := do
  let args := operation.getAppArgs
  unless operation.isAppOfArity ``Norm.norm 3 do
    throwError "unsupported norm bound {operation}"
  let vector := args[2]!
  let proof ← if let some n ← realVectorDimension? (← inferType vector) then
      representationProof (← mkAppOptM ``Morew.Rewrite.normInfEpigraph #[some n])
        vector bound
    else do
      let vector ← Affine.reduceStructure vector
      unless vector.isAppOfArity ``WithLp.toLp 3 do
        throwError "expected the native norm of Fin n → ℝ or WithLp.toLp 1/∞ of such a vector"
      let lpArgs := vector.getAppArgs
      let some n ← realVectorDimension? (← inferType lpArgs[2]!) |
        throwError "expected a Fin n → ℝ vector inside WithLp.toLp"
      let saved ← saveState
      let topProof ← representationProof
        (← mkAppOptM ``Morew.Rewrite.normInfToLpEpigraph #[some n]) lpArgs[2]! bound
      let (topSource, _) ← theoremSides topProof
      let expectedTop ← Affine.reduceStructure topSource.getAppArgs[2]!
      if ← isDefEq vector expectedTop.getAppArgs[2]! then
        pure topProof
      else
        saved.restore
        let oneProof ← representationProof
          (← mkAppOptM ``Morew.Rewrite.norm1Epigraph #[some n]) lpArgs[2]! bound
        let (oneSource, _) ← theoremSides oneProof
        let expectedOne ← Affine.reduceStructure oneSource.getAppArgs[2]!
        unless ← isDefEq vector expectedOne.getAppArgs[2]! do
          throwError "unsupported norm exponent; expected 1 or ∞"
        pure oneProof
  let (source, _) ← theoremSides proof
  sameOperationPrefix operation (← Affine.reduceStructure source.getAppArgs[2]!) 1
  return proof

private def automaticProof (point body : Expr) (selected? : Option Rule := none) :
    MetaM Expr := do
  let body ← Affine.reduceStructure body
  let greaterEqual := body.isAppOfArity ``GE.ge 4
  unless greaterEqual || body.isAppOfArity ``LE.le 4 do
    throwError "no supported exact polyhedral rule for {body}; expected an upper epigraph bound or lower hypograph bound"
  let args := body.getAppArgs
  unless ← isDefEq args[0]! (mkConst ``Real) do
    throwError "expected a real scalar bound for an exact polyhedral rule"
  unless ← isDefEq args[1]! (mkConst ``Real.instLE) do
    throwError "unsupported order instance in the selected predicate"
  let left ← Affine.reduceStructure args[if greaterEqual then 3 else 2]!
  let right ← Affine.reduceStructure args[if greaterEqual then 2 else 3]!
  let accepts := fun rule => selected?.isNone || selected? == some rule
  if let some operation ← Atom.recognizeAtom? left then
    let operands := operation.operands
    match operation.kind with
    | .abs =>
        if accepts .absolute then
          return ← representationProof (mkConst ``Morew.Rewrite.absEpigraph) operands[0]! right
    | .pos =>
        if accepts .positivePart then
          return ← representationProof (mkConst ``Morew.Rewrite.posEpigraph) operands[0]! right
    | .maximum =>
        if accepts .maximum then
          let input ← mkAppM ``Prod.mk #[operands[0]!, operands[1]!]
          return ← representationProof (mkConst ``Morew.Rewrite.maxEpigraph) input right
    | _ => pure ()
  if let some operation ← Atom.recognizeAtom? right then
    if operation.kind == .minimum && accepts .minimum then
      let input ← mkAppM ``Prod.mk #[operation.operands[0]!, operation.operands[1]!]
      return ← representationProof (mkConst ``Morew.Rewrite.minHypograph) input left true
  if left.isAppOfArity ``Finset.sup' 6 && accepts .supremum then
    return ← finiteExtremumProof point left right false
  if right.isAppOfArity ``Finset.inf' 6 && accepts .infimum then
    return ← finiteExtremumProof point right left true
  if left.isAppOfArity ``Norm.norm 3 && accepts .norm then
    return ← normProof left right
  throwError "no supported exact polyhedral rule for {body}; expected abs, positive part, maximum, minimum, a finite extremum, or a supported norm in its exact orientation"

private def automaticLift (selected? : Option Rule) (source domain : Expr) : MetaM Expr :=
  withLocalDeclD `point domain fun point => do
    let body ← Affine.reduceStructure (mkApp source point)
    let proof ← automaticProof point body selected?
    let (provedSource, target) ← theoremSides proof
    unless ← isDefEq provedSource body do
      throwError "the exact rule does not describe the entire selected predicate"
    let pointwise ← mkLambdaFVars #[point] proof
    let lift ← if target.isAppOfArity ``Exists 2 then do
        let args := target.getAppArgs
        let auxiliary ← whnf args[0]!
        if ← Affine.depends point auxiliary then
          throwError "the auxiliary type depends on a decision variable"
        let target ← mkLambdaFVars #[point] args[1]!
        mkAppM ``Morew.ExactConstraintLift.mk #[auxiliary, target, pointwise]
      else do
        let target ← mkLambdaFVars #[point] target
        mkAppM ``Morew.ExactConstraintLift.ofIff #[target, pointwise]
    checkLift source lift

/-- Plan an exact polyhedral replacement or certify an explicit representation. -/
def plan (sourcePredicate : Expr) (rule? : Option Expr := none)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError Result) :=
  Plan.plan (automaticLift none) sourcePredicate rule? provider

/-- Certify one native rule without falling through to another operation. -/
def planRule (rule : Rule) (sourcePredicate : Expr) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Affine.AffineError Result) :=
  Plan.plan (automaticLift (some rule)) sourcePredicate none provider

end Morew.Elab.Conic.Polyhedral
