/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Replace
import Morew.Elab.Substitution.Evidence

/-!
# Checked removal of a selected constraint

Only complete retained rows supply duplicate evidence. Tautologies use a fixed
set of unconditional facts; arbitrary retained-context implications are checked
separately and never added to the normalization simplifier.
-/

namespace Morew.Elab.Reformulation.Remove

open Lean Lean.Meta
open Morew.Elab.Rewrite.Decomposition

private def complete (expression : Expr) : MetaM Bool := do
  return !(← Expr.hasUnresolved expression) &&
    !(← Evidence.hasPlaceholders expression)

private def retainedRows (presentation : PresentationState) (index : Nat) : Array Expr :=
  (presentation.constraints.extract 0 index ++
    presentation.constraints.extract (index + 1) presentation.constraints.size).map (·.predicate)

/-- The exact proof contract, formed from current rows with the selected row excluded. -/
def implicationType (presentation : PresentationState) (index : Nat) : MetaM Expr := do
  unless index < presentation.constraints.size do
    throwError "constraint removal index is out of bounds"
  let rows := retainedRows presentation index
  withLocalDeclD `point presentation.domainType fun point => do
    let retained := conjunction (rows.toList.map (mkApp · point))
    mkForallFVars #[point]
      (← mkArrow retained (mkApp presentation.constraints[index]!.predicate point))

private def matchingProof? (goal : Expr) (action : MetaM Expr) : MetaM (Option Expr) := do
  let result ← State.withIsolatedMVars do
    try
      let proof ← instantiateMVars (← action)
      unless (← complete proof) && (← isDefEq (← inferType proof) goal) do
        return .error ()
      checkWithKernel proof
      return .ok proof
    catch _ => return .error ()
  return result.toOption

-- Data instances are taken from the source operations, not incidental operand
-- computations. Proof-valued compatibility classes may still justify those
-- operations; the complete theorem conclusion must match the original goal.
private def withSourceInstances (operations : Array Expr) (action : MetaM Expr) :
    MetaM Expr := do
  let instances ← (← getLocalInstances).filterM fun localInst => do
    if ← isProp (← inferType localInst.fvar) then return true
    operations.anyM (Expr.depends localInst.fvar ·)
  withLCtx (← getLCtx) instances action

private partial def tautology? (goal : Expr) : MetaM (Option Expr) := do
  let body ← Substitution.Evidence.predicateView goal 32
  if body.isConstOf ``True then return some (mkConst ``True.intro)
  if body.isAppOfArity ``And 2 then
    let some left ← tautology? body.getAppArgs[0]! | return none
    let some right ← tautology? body.getAppArgs[1]! | return none
    return some (← mkAppM ``And.intro #[left, right])
  if body.isAppOfArity ``Eq 3 then
    return ← matchingProof? goal (mkEqRefl body.getAppArgs[1]!)
  let reversed := body.isAppOfArity ``GE.ge 4 || body.isAppOfArity ``GT.gt 4
  let weak := body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``GE.ge 4
  let strict := body.isAppOfArity ``LT.lt 4 || body.isAppOfArity ``GT.gt 4
  unless weak || strict do return none
  let args := body.getAppArgs
  let left := args[if reversed then 3 else 2]!
  let right ← Expr.reduceStructure args[if reversed then 2 else 3]!
  if weak then
    let order ← Expr.reduceStructure args[1]!
    -- A captured preorder need not be the currently registered instance.
    if order.isAppOfArity ``Preorder.toLE 2 then
      if let some proof ← matchingProof? goal
          (mkAppOptM ``le_refl
            #[some args[0]!, some order.getAppArgs[1]!, some left]) then
        return some proof
    if let some proof ← matchingProof? goal
        (withSourceInstances #[args[1]!] (mkAppM ``le_refl #[left])) then
      return some proof
    if right.isAppOfArity ``HPow.hPow 6 || right.isAppOfArity ``Pow.pow 5 then
      let arguments := right.getAppArgs
      let operation := mkAppN right.getAppFn (arguments.extract 0 (arguments.size - 2))
      return ← matchingProof? goal
        (withSourceInstances #[args[1]!, left, operation]
          (mkAppM ``sq_nonneg #[arguments[arguments.size - 2]!]))
  else if right.isAppOfArity ``Real.exp 1 then
    return ← matchingProof? goal (mkAppM ``Real.exp_pos #[right.getAppArgs[0]!])
  return none

/-- Prove a selected duplicate or basic tautology without assigning caller
metavariables. No ambient facts, retained-row subexpressions, or historical
constraints participate in the search. -/
def prove? (presentation : PresentationState) (index : Nat) : MetaM (Option Expr) := do
  let result ← State.withIsolatedMVars do
    try
      let expected ← implicationType presentation index
      unless ← complete expected do return .error ()
      let selected := presentation.constraints[index]!.predicate
      let rows := retainedRows presentation index
      let proof? ← withLocalDeclD `point presentation.domainType fun point => do
        let retained := conjunction (rows.toList.map (mkApp · point))
        withLocalDeclD `retained retained fun evidence => do
          let parts ← conjunctionParts rows.size evidence
          for row in rows, part in parts do
            let same ← withoutModifyingState (isDefEq selected row)
            if same then return some (← mkLambdaFVars #[point, evidence] part)
          let some proof ← tautology? (mkApp selected point) | return none
          return some (← mkLambdaFVars #[point, evidence] proof)
      let some proof := proof? | return .error ()
      let proof ← instantiateMVars proof
      unless (← complete proof) && (← isDefEq (← inferType proof) expected) do
        return .error ()
      checkWithKernel proof
      return .ok proof
    catch _ => return .error ()
  return result.toOption

private def applyRemovalCore (presentation : PresentationState) (index : Nat)
    (implied : Expr) : MetaM Replace.RewriteResult := do
  withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
    for expression in #[presentation.domainType, presentation.valueType,
        presentation.objective] ++ presentation.binders.map (·.type) do
      unless ← complete expression do
        throwError "constraint removal presentation contains unresolved metavariables or placeholders"
    let expected ← implicationType presentation index
    unless (← complete implied) && (← complete expected) do
      throwError "constraint removal proof contains unresolved metavariables or placeholders"
    unless ← isDefEq (← inferType implied) expected do
      throwError "constraint removal proof does not match the selected row and retained constraints"
    checkWithKernel implied
    let source ← presentation.canonicalProblem
    let decomposition ← Replace.makeDecomposition presentation index source
    let equivalence ← instantiateMVars (← mkAppM ``Morew.removeConstraintEquivalence
      #[source, decomposition, implied])
    let next := { presentation with constraints :=
      presentation.constraints.extract 0 index ++
        presentation.constraints.extract (index + 1) presentation.constraints.size }
    let targetProblem ← instantiateMVars (← next.canonicalProblem)
    let expected ← mkAppM ``Morew.GlobalEquivalence #[source, targetProblem]
    unless ← isDefEq (← inferType equivalence) expected do
      throwError "constraint removal did not produce the retained canonical problem"
    unless (← complete equivalence) && (← complete targetProblem) do
      throwError "constraint removal contains unresolved metavariables or placeholders"
    checkWithKernel equivalence
    return { targetProblem, equivalence }

/-- Apply an implication checked against exactly the current retained rows.
The resulting canonical problem preserves every other row and all coordinates.
Incomplete presentations are rejected, and caller metavariables remain unchanged
even if typeclass synthesis or canonical presentation validation fails. -/
def applyRemoval (presentation : PresentationState) (index : Nat)
    (implied : Expr) : MetaM Replace.RewriteResult := do
  let result ← State.withIsolatedMVars (ε := Empty) do
    return .ok (← applyRemovalCore presentation index implied)
  match result with
  | .ok result => return result
  | .error impossible => nomatch impossible

end Morew.Elab.Reformulation.Remove
