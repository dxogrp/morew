import Morew.Elab.Conic.Plan

/-!
# Retained lower bounds for exact conic rewrites

Only independent constants with checked sign evidence, or native non-strict
lower bounds in retained entries, establish a domain fact. Search preserves
presentation order and conjunction boundaries. Strict rows, arithmetic
deductions, and the selected predicate are not additional sources of evidence.
-/

namespace Morew.Elab.Conic.Domain

open Lean Lean.Meta Qq

/-- Project the ordered entries of the canonical retained conjunction. -/
def conjunctionParts (count : Nat) (proof : Expr) : MetaM (Array Expr) := do
  if count == 0 then return #[]
  let mut parts := #[]
  let mut rest := proof
  for _ in [:count - 1] do
    parts := parts.push (← mkAppM ``And.left #[rest])
    rest ← mkAppM ``And.right #[rest]
  return parts.push rest

private theorem nonnegativeOfPositive {value : ℝ} (h : 0 < value) : 0 ≤ value :=
  le_of_lt h

/-- Prove the sign of an independent real constant from an independent local
hypothesis or bounded numeral/rational evaluation, using canonical real order. -/
def constantSign? (point value : Expr) (strict : Bool) : MetaM (Option Expr) := do
  if (← Affine.depends point value) || (← Plan.unresolved value) then return none
  let value : Q(ℝ) := value
  let obligation : Q(Prop) := if strict then q(0 < $value) else q(0 ≤ $value)
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if !(← Affine.depends point declaration.toExpr) &&
          !(← Plan.unresolved declaration.toExpr) then
        if ← isDefEq declaration.type obligation then
          checkWithKernel declaration.toExpr
          return some declaration.toExpr
        if !strict && (← isDefEq declaration.type q(0 < $value)) then
          let proof ← mkAppM ``nonnegativeOfPositive #[declaration.toExpr]
          checkWithKernel proof
          return some proof
  try
    let context ← readThe Core.Context
    let localLimit := (← IO.getNumHeartbeats) - context.initHeartbeats + 2_000_000
    let limit := if context.maxHeartbeats == 0 then localLimit
      else min context.maxHeartbeats localLimit
    let proof ← mapLetDeclZeta `_marginLE q(LE ℝ) q(inferInstance : LE ℝ) fun _ => do
      mapLetDeclZeta `_marginOrder q(LT ℝ) q(inferInstance : LT ℝ) fun _ => do
      mapLetDeclZeta `_marginPreorder q(Preorder ℝ) q(inferInstance : Preorder ℝ) fun _ => do
      mapLetDeclZeta `_marginPartialOrder q(PartialOrder ℝ)
        q(inferInstance : PartialOrder ℝ) fun _ => do
      let result ← withTheReader Core.Context
        (fun context => { context with maxHeartbeats := limit }) <|
        Mathlib.Meta.NormNum.deriveBool obligation
      match result with
      | ⟨true, proof⟩ => pure proof
      | _ => throwError "constant sign was not established"
    checkWithKernel proof
    return some proof
  catch _ => return none

private theorem positiveOfMargin {epsilon value : ℝ}
    (positive : 0 < epsilon) (bound : epsilon ≤ value) : 0 < value :=
  lt_of_lt_of_le positive bound

private theorem nonnegativeOfMargin {epsilon value : ℝ}
    (nonnegative : 0 ≤ epsilon) (bound : epsilon ≤ value) : 0 ≤ value :=
  le_trans nonnegative bound

private partial def signInRow? (point value body evidence : Expr) (strict : Bool) :
    MetaM (Option Expr) := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  if let .letE name type initial rest nondep := body then
    if (← Affine.depends point type) || (← Affine.depends point initial) then
      return ← signInRow? point value (rest.instantiate1 initial) evidence strict
    return ← withLetDecl name type initial (nondep := nondep) fun binding => do
      let proof? ← signInRow? point value (rest.instantiate1 binding) evidence strict
      proof?.mapM fun proof => proof.replaceFVarsM #[binding] #[initial]
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    if let some proof ← signInRow? point value args[0]!
        (← mkAppM ``And.left #[evidence]) strict then return some proof
    return ← signInRow? point value args[1]!
      (← mkAppM ``And.right #[evidence]) strict
  let ge := body.isAppOfArity ``GE.ge 4
  unless ge || body.isAppOfArity ``LE.le 4 do return none
  let args := body.getAppArgs
  unless (← isDefEq args[0]! q(ℝ)) &&
      (← isDefEq args[1]! (mkConst ``Real.instLE)) do return none
  let epsilon := args[if ge then 3 else 2]!
  let upper ← Affine.reduceStructure args[if ge then 2 else 3]!
  unless ← isDefEq upper value do return none
  let some sign ← constantSign? point epsilon strict | return none
  return some (← mkAppM
    (if strict then ``positiveOfMargin else ``nonnegativeOfMargin) #[sign, evidence])

/-- Certify strict or non-strict nonnegativity from an independent constant or
the first usable retained lower margin. The caller excludes the selected row. -/
def signFromRetained? (point value : Expr) (retainedBodies : Array Expr)
    (remainderProof : Expr) (strict : Bool) : MetaM (Option Expr) := do
  if let some proof ← constantSign? point value strict then return some proof
  let parts ← conjunctionParts retainedBodies.size remainderProof
  for body in retainedBodies, proof in parts do
    if let some sign ← signInRow? point value body proof strict then return some sign
  return none

end Morew.Elab.Conic.Domain
