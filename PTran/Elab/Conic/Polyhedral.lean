import PTran.Conic.Polyhedral
import PTran.Elab.Atom
import PTran.Elab.Conic.Plan

/-!
# Checked plans for exact polyhedral constraint replacements

Native polyhedral recognition shares custom-rule adaptation and row certification
with the other conic planners.
-/

namespace PTran.Elab.Conic.Polyhedral

open Lean Lean.Meta
open Plan

/-- A checked exact replacement, before presentation names are allocated. -/
abbrev Result := Plan.Result

/-- Independently selectable native rules. Norm carriers select disjoint variants. -/
inductive Rule where
  | absolute | positivePart | maximum | minimum | supremum | infimum | norm
  deriving BEq, Repr

/-- Stable order for exhaustive native-rule certification. -/
def rules : Array Rule :=
  #[.absolute, .positivePart, .maximum, .minimum, .supremum, .infimum, .norm]

private def isRealVector (type : Expr) : MetaM Bool := do
  let type ← whnf type
  let .forallE _ index body _ := type | return false
  if body.hasLooseBVars then return false
  return (← whnf index).isAppOfArity ``Fin 1 && (← whnf body).isConstOf ``Real

private def theoremSides (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← inferType proof
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
  let theoremName := if minimum then ``PTran.Conic.Polyhedral.le_inf'_iff
    else ``PTran.Conic.Polyhedral.sup'_le_iff
  let proof ← mkAppM theoremName #[args[3]!, args[4]!, args[5]!, bound]
  let (lhs, _) ← theoremSides proof
  let expected := lhs.getAppArgs[if minimum then 3 else 2]!
  sameOperationPrefix operation expected 3
  return proof

private def normProof (operation bound : Expr) : MetaM Expr := do
  let args := operation.getAppArgs
  unless operation.isAppOfArity ``Norm.norm 3 do
    throwError "unsupported norm bound {operation}"
  let vector := args[2]!
  let proof ← if ← isRealVector (← inferType vector) then
      mkAppM ``PTran.Conic.Polyhedral.norm_le_iff #[vector, bound]
    else do
      let vector ← Affine.reduceStructure vector
      unless vector.isAppOfArity ``WithLp.toLp 3 do
        throwError "expected the native norm of Fin n → ℝ or WithLp.toLp 1/∞ of such a vector"
      let lpArgs := vector.getAppArgs
      unless ← isRealVector (← inferType lpArgs[2]!) do
        throwError "expected a Fin n → ℝ vector inside WithLp.toLp"
      let saved ← saveState
      let topProof ← mkAppM ``PTran.Conic.Polyhedral.norm_toLp_top_le_iff
        #[lpArgs[2]!, bound]
      let (topSource, _) ← theoremSides topProof
      let expectedTop := topSource.getAppArgs[2]!
      if ← isDefEq vector expectedTop.getAppArgs[2]! then
        pure topProof
      else
        saved.restore
        let oneProof ← mkAppM ``PTran.Conic.Polyhedral.norm_toLp_one_le_iff
          #[lpArgs[2]!, bound]
        let (oneSource, _) ← theoremSides oneProof
        unless ← isDefEq vector oneSource.getAppArgs[2]!.getAppArgs[2]! do
          throwError "unsupported norm exponent; expected 1 or ∞"
        pure oneProof
  let (source, _) ← theoremSides proof
  sameOperationPrefix operation source.getAppArgs[2]! 1
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
          return ← mkAppM ``PTran.Conic.Polyhedral.abs_le_iff #[operands[0]!, right]
    | .pos =>
        if accepts .positivePart then
          return ← mkAppM ``PTran.Conic.Polyhedral.posPart_le_iff #[operands[0]!, right]
    | .maximum =>
        if accepts .maximum then
          return ← mkAppM ``PTran.Conic.Polyhedral.max_le_iff
            #[operands[0]!, operands[1]!, right]
    | _ => pure ()
  if let some operation ← Atom.recognizeAtom? right then
    if operation.kind == .minimum && accepts .minimum then
      return ← mkAppM ``PTran.Conic.Polyhedral.le_min_iff
        #[operation.operands[0]!, operation.operands[1]!, left]
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
        if ← Affine.depends point args[0]! then
          throwError "the auxiliary type depends on a decision variable"
        let target ← mkLambdaFVars #[point] args[1]!
        mkAppM ``PTran.ExactConstraintLift.mk #[args[0]!, target, pointwise]
      else do
        let target ← mkLambdaFVars #[point] target
        mkAppM ``PTran.ExactConstraintLift.ofIff #[target, pointwise]
    checkLift source lift

/-- Plan an exact polyhedral replacement or certify an explicit representation. -/
def plan (sourcePredicate : Expr) (rule? : Option Expr := none)
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Result) :=
  Plan.plan (automaticLift none) sourcePredicate rule? config

/-- Certify one native rule without falling through to another operation. -/
def planRule (rule : Rule) (sourcePredicate : Expr) (config : Affine.Config := {}) :
    MetaM (Except Affine.AffineError Result) :=
  Plan.plan (automaticLift (some rule)) sourcePredicate none config

end PTran.Elab.Conic.Polyhedral
