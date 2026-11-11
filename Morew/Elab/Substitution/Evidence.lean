/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Evidence.Sign

/-! Prove coverage from complete source feasibility. Declaration premises use only independent
ambient facts preceding the source point. Search typed facts, conjunctions, sign weakening,
independent lower margins, and bounded numerical evidence. -/

namespace Morew.Elab.Substitution.Evidence

open Lean Lean.Meta Qq

private def complete (expression : Expr) : MetaM Bool := do
  return !(← Expr.hasUnresolved expression) &&
    !(← Morew.Elab.Evidence.hasPlaceholders expression)

/-- Expose bounded predicate aliases and record fields while preserving comparison and membership heads. -/
def predicateView (type : Expr) : Nat → MetaM Expr
  | 0 => pure type
  | fuel + 1 => do
    let type ← Expr.reduceStructure type
    if let some name := type.getAppFn.constName? then
      if #[``And, ``True, ``False, ``Eq, ``Ne, ``Not, ``LE.le, ``LT.lt, ``GE.ge,
          ``GT.gt, ``Membership.mem].contains name then return type
    if let some projection ← reduceProj? type.getAppFn then
      return ← predicateView (mkAppN projection type.getAppArgs) fuel
    if let some expanded ← unfoldDefinition? type then
      return ← predicateView expanded fuel
    return type

private partial def projection? (proof goal : Expr) : MetaM (Option Expr) := do
  let type ← predicateView (← inferType proof) 32
  if ← isDefEq type goal then return some proof
  if type.isAppOfArity ``And 2 then
    if let some found ← projection? (← mkAppM ``And.left #[proof]) goal then
      return some found
    return ← projection? (← mkAppM ``And.right #[proof]) goal
  return none

private partial def leaves (proof : Expr) : MetaM (Array Expr) := do
  let type ← predicateView (← inferType proof) 32
  if type.isAppOfArity ``And 2 then
    return (← leaves (← mkAppM ``And.left #[proof])) ++
      (← leaves (← mkAppM ``And.right #[proof]))
  return #[proof]

/-- Hide source facts and project independent ambient conjunctions for sign search. -/
private def withAmbientEvidence (point : Expr) (action : MetaM (Option Expr)) :
    MetaM (Option Expr) := do
  let original ← getLCtx
  let mut context := original
  let mut afterPoint := false
  let mut facts := #[]
  for declaration in original do
    if declaration.fvarId == point.fvarId! then afterPoint := true
    if afterPoint then context := context.setKind declaration.fvarId .implDetail
    else if !declaration.isImplementationDetail && (← isProp declaration.type) then
      let proof := declaration.toExpr
      if (← complete proof) && !(← Expr.depends point proof) then
        for leaf in ← leaves proof do
          facts := facts.push (← predicateView (← inferType leaf) 32, leaf)
  let rec expose (remaining : List (Expr × Expr)) : MetaM (Option Expr) := do
    match remaining with
    | [] => action
    | (type, proof) :: rest =>
      withLetDecl `ambientEvidence type proof fun fact => do
        let result ← expose rest
        result.mapM fun result => mkLetFVars #[fact] result
  withLCtx' context (expose facts.toList)

private def direct? (point goal : Expr) (feasible? : Option Expr) : MetaM (Option Expr) := do
  if let some feasible := feasible? then
    if let some proof ← projection? feasible goal then return some proof
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let proof := declaration.toExpr
    if (← Expr.depends point proof) || !(← complete proof) then continue
    unless ← isProp declaration.type do continue
    if let some proof ← projection? proof goal then return some proof
  return none

private theorem nonnegOfPositive {value : ℝ} (h : 0 < value) : 0 ≤ value :=
  le_of_lt h

private theorem nonzeroOfPositive {value : ℝ} (h : 0 < value) : value ≠ 0 :=
  ne_of_gt h

private theorem nonzeroOfNegative {value : ℝ} (h : value < 0) : value ≠ 0 :=
  ne_of_lt h

private theorem reverseNonzero {value : ℝ} (h : value ≠ 0) : (0 : ℝ) ≠ value :=
  Ne.symm h

private def sign? (point value : Expr) (strict : Bool) (feasible? : Option Expr) :
    MetaM (Option Expr) := do
  let value : Q(ℝ) ← Expr.reduceStructure value
  let goal : Q(Prop) := if strict then q(0 < $value) else q(0 ≤ $value)
  if let some proof ← direct? point goal feasible? then return some proof
  if !strict then
    if let some proof ← direct? point q(0 < $value) feasible? then
      return some (← mkAppM ``nonnegOfPositive #[proof])
  if let some proof ← Morew.Elab.Evidence.constantSign? point value strict then return some proof
  if let some feasible := feasible? then
    for proof in ← leaves feasible do
      if let some result ← Morew.Elab.Evidence.Sign.signFromRetained? point value
          #[← predicateView (← inferType proof) 32] proof strict then return some result
  return none

private def realComparison? (goal : Expr) : MetaM (Option (Bool × Expr × Expr)) := do
  let strict := goal.isAppOfArity ``LT.lt 4 || goal.isAppOfArity ``GT.gt 4
  let reversed := goal.isAppOfArity ``GE.ge 4 || goal.isAppOfArity ``GT.gt 4
  unless strict || reversed || goal.isAppOfArity ``LE.le 4 do return none
  let args := goal.getAppArgs
  unless ← isDefEq args[0]! q(ℝ) do return none
  let left : Q(ℝ) := args[if reversed then 3 else 2]!
  let right : Q(ℝ) := args[if reversed then 2 else 3]!
  let canonical : Q(Prop) := if strict then q($left < $right) else q($left ≤ $right)
  unless ← isDefEq goal canonical do return none
  return some (strict, left, right)

private def nonzeroValue? (goal : Expr) : MetaM (Option (Expr × Bool)) := do
  let args ← if goal.isAppOfArity ``Ne 3 then pure goal.getAppArgs
    else if goal.isAppOfArity ``Not 1 then do
      let equality := goal.getAppArgs[0]!
      unless equality.isAppOfArity ``Eq 3 do return none
      pure equality.getAppArgs
    else if let .forallE _ equality body _ := goal then do
      unless body.isConstOf ``False && equality.isAppOfArity ``Eq 3 do return none
      pure equality.getAppArgs
    else return none
  unless ← isDefEq args[0]! q(ℝ) do return none
  let left : Q(ℝ) := args[1]!
  let right : Q(ℝ) := args[2]!
  if (← isDefEq right q((0 : ℝ))) && (← isDefEq goal q($left ≠ 0)) then
    return some (← Expr.reduceStructure left, false)
  if (← isDefEq left q((0 : ℝ))) && (← isDefEq goal q((0 : ℝ) ≠ $right)) then
    return some (← Expr.reduceStructure right, true)
  return none

private partial def proveCore? (point goal : Expr) (feasible? : Option Expr) :
    MetaM (Option Expr) := do
  if let some proof ← direct? point goal feasible? then return some proof
  let goal ← predicateView goal 32
  if goal.isConstOf ``True then return some (mkConst ``True.intro)
  if goal.isAppOfArity ``And 2 then
    let args := goal.getAppArgs
    let some left ← proveCore? point args[0]! feasible? | return none
    let some right ← proveCore? point args[1]! feasible? | return none
    return some (← mkAppM ``And.intro #[left, right])
  if let some (strict, left, right) ← realComparison? goal then
    if ← isDefEq left q((0 : ℝ)) then return ← sign? point right strict feasible?
    -- Check independent numerical comparisons with their actual order instances.
    return ← Morew.Elab.Evidence.proveIndependent? point goal
  if let some (value, reverse) ← nonzeroValue? goal then
    let value : Q(ℝ) := value
    let proof? ← if let some proof ← direct? point q($value ≠ 0) feasible? then
        pure (some proof)
      else if let some proof ← direct? point q((0 : ℝ) ≠ $value) feasible? then
        pure (some (← mkAppM ``Ne.symm #[proof]))
      else
        match ← sign? point value true feasible? with
        | some positive => pure (some (← mkAppM ``nonzeroOfPositive #[positive]))
        | none => do
          let some negative ← proveCore? point q($value < 0) feasible? | pure none
          pure (some (← mkAppM ``nonzeroOfNegative #[negative]))
    return ← proof?.mapM fun proof =>
      if reverse then mkAppM ``reverseNonzero #[proof] else pure proof
  return none

private def checked? (point goal : Expr) (feasible? : Option Expr) : MetaM (Option Expr) := do
  let result ← State.withIsolatedMVars do
    try
      unless point.isFVar && (← complete goal) do return .error ()
      if let some feasible := feasible? then
        unless ← complete feasible do return .error ()
      else if ← Expr.depends point goal then return .error ()
      let some proof ← withAmbientEvidence point (proveCore? point goal feasible?)
        | return .error ()
      let proof ← instantiateMVars proof
      unless (← complete proof) && (← isDefEq (← inferType proof) goal) do return .error ()
      if feasible?.isNone && (← Expr.depends point proof) then return .error ()
      checkWithKernel proof
      return .ok proof
    catch _ => return .error ()
  return result.toOption

/-- Prove parameterization range from source feasibility and independent ambient facts.
The fresh source point follows ambient declarations. Kernel-check the result and
preserve caller metavariables; restore declarations on failure. -/
def proveRange? (point goal feasibleEvidence : Expr) : MetaM (Option Expr) :=
  checked? point goal (some feasibleEvidence)

/-- Prove a declaration premise without source feasibility. Only independent
ambient facts preceding the fresh point, their conjunction projections, checked
real sign consequences, and bounded numerical evidence are available. -/
def proveIndependent? (point goal : Expr) : MetaM (Option Expr) :=
  checked? point goal none

end Morew.Elab.Substitution.Evidence
