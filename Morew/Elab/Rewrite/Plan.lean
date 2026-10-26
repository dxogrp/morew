/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Elab.Affine
import Morew.Elab.Rewrite.Decomposition

/-!
# Shared exact replacement planning data

Conic and smooth planners share exact-lift adaptation, scoped evidence, and the
checked relation between a lift target and its ordered rows. Each planner keeps
its own target exposure, supported-space checks, and row certification policy.
This module neither recognizes operations nor certifies affine or smooth rows.
-/

namespace Morew.Elab.Rewrite.Plan

open Lean Lean.Meta

/-- The exact replacement data shared by target-specific planners. -/
structure Result where
  /-- A checked exact lift of the complete selected predicate. -/
  lift : Expr
  /-- The auxiliary type, with definitionally `Unit` auxiliaries erased. -/
  auxiliary? : Option Expr
  /-- The original decision domain, or its product with the auxiliary type. -/
  nextDomain : Expr
  /-- Replacement predicates in deterministic conjunction order. -/
  rowPredicates : Array Expr
  /-- The instantiated lift target is equivalent to the row conjunction. -/
  targetIff : Expr

/-- Substitute scoped evidence through every expression in an exact replacement. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result :=
  let replace := fun expression : Expr => expression.replaceFVars oldVars newVars
  { lift := replace result.lift
    auxiliary? := result.auxiliary?.map replace
    nextDomain := replace result.nextDomain
    rowPredicates := result.rowPredicates.map replace
    targetIff := replace result.targetIff }

/-- Retain finite-index evidence and substitute it through the completed result. -/
def withScopedFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (instances : List Expr) (action : MetaM α) : MetaM α := do
  match instances with
  | [] => action
  | inst :: rest =>
    withLetDecl `_conicFinite (← inferType inst) inst fun binding => do
      let result ← withScopedFiniteInstances replace rest action
      return replace result #[binding] #[inst]

/-- Retain independent source lets throughout certificate construction. -/
partial def withScopedEvidence {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (point body : Expr) (action : MetaM α) : MetaM α := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← withScopedEvidence replace point (rest.instantiate1 value) action
    withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← withScopedEvidence replace point (rest.instantiate1 binding) action
      return replace result #[binding] #[value]
  else action

-- Do not let unification specialize a caller's unresolved local declarations.
/-- Detect unresolved expressions, including evidence hidden in local declarations. -/
partial def unresolved (expression : Expr) (seen : FVarIdSet := {}) :
    MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then return true
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    unless seen.contains id do
      seen := seen.insert id
      let declaration ← id.getDecl
      if ← unresolved declaration.type seen then return true
      if let some value := declaration.value? (allowNondep := true) then
        if ← unresolved value seen then return true
  return false

/-- Read the decision domain of a fully elaborated predicate. -/
def predicateDomain (predicate : Expr) : MetaM Expr := do
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | throwError "expected a predicate on the current decision domain"
  unless codomain == mkSort .zero do
    throwError "expected a predicate on the current decision domain"
  return domain

/-- Check that a supplied lift describes the complete selected predicate. -/
def checkLift (source lift : Expr) : MetaM Expr := do
  let type ← whnf (← inferType lift)
  unless type.isAppOfArity ``Morew.ExactConstraintLift 2 do
    throwError "expected an exact constraint lift"
  unless ← isDefEq type.getAppArgs[1]! source do
    throwError "the supplied exact certificate does not describe the entire selected predicate"
  let lift ← instantiateMVars lift
  if ← unresolved lift then
    throwError "the exact certificate contains unresolved metavariables; supply its input and bound maps explicitly"
  checkWithKernel lift
  return lift

private def adaptRepresentation (source domain rule : Expr) (adapter : Name)
    (inputType outputType : Expr) : MetaM Expr := do
  let input ← mkFreshExprMVar (← mkArrow domain inputType)
  let output ← mkFreshExprMVar (← mkArrow domain outputType)
  let lift ← mkAppM adapter #[rule, input, output]
  checkLift source lift

/-- Adapt one of the supported exact representation records to a selected predicate. -/
def customLift (source domain rule : Expr) : MetaM Expr := do
  let type ← whnf (← inferType rule)
  let args := type.getAppArgs
  if type.isAppOfArity ``Morew.ExactConstraintLift 2 then
    return ← checkLift source rule
  if type.isAppOfArity ``Morew.GraphRepresentation 3 then
    let saved ← saveState
    try
      return ← adaptRepresentation source domain rule
        ``Morew.GraphRepresentation.toExactConstraintLift args[0]! args[1]!
    catch _ =>
      saved.restore
      return ← adaptRepresentation source domain rule
        ``Morew.GraphRepresentation.toExactConstraintLiftSymm args[0]! args[1]!
  if type.isAppOfArity ``Morew.EpigraphRepresentation 4 then
    return ← adaptRepresentation source domain rule
      ``Morew.EpigraphRepresentation.toExactConstraintLift args[0]! args[1]!
  if type.isAppOfArity ``Morew.HypographRepresentation 4 then
    return ← adaptRepresentation source domain rule
      ``Morew.HypographRepresentation.toExactConstraintLift args[0]! args[1]!
  throwError "expected an ExactConstraintLift, GraphRepresentation, EpigraphRepresentation, or HypographRepresentation for the entire selected predicate"

/-- Check the exact target equivalence without reducing or certifying its rows.

The expected proposition retains the supplied lift, decision layout, and row
order. Target-specific planners choose when to run this check; in particular,
smooth planning checks exactness before using generated rows as domain evidence.
-/
def Result.checkTargetIff (result : Result)
    (mismatchMessage : MessageData :=
      "internal error: target decomposition does not match the exact lift") : MetaM Unit := do
  let expected ← withLocalDeclD `point result.nextDomain fun point => do
    let target ← match result.auxiliary? with
      | none =>
        mkAppM ``Morew.ExactConstraintLift.target #[result.lift, point, mkConst ``Unit.unit]
      | some _ =>
        mkAppM ``Morew.ExactConstraintLift.target
          #[result.lift, .proj ``Prod 0 point, .proj ``Prod 1 point]
    let rows := result.rowPredicates.toList.map (mkApp · point)
    mkForallFVars #[point]
      (mkApp2 (mkConst ``Iff) target (Decomposition.conjunction rows))
  unless ← isDefEq (← inferType result.targetIff) expected do
    throwError mismatchMessage
  checkWithKernel result.targetIff

end Morew.Elab.Rewrite.Plan
