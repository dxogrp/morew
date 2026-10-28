/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Elab.Expr
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

/-- Exactness is either unconditional or checked under precisely the retained
constraints. Contextual targets have a uniform auxiliary type and do not take
a retained-feasibility proof as an argument. -/
inductive Certificate where
  | exact (lift : Expr)
  | contextual (auxiliary target sourceIffExists : Expr)

/-- The proof-bearing expression shared when storing a replacement. -/
def Certificate.expression : Certificate → Expr
  | .exact lift => lift
  | .contextual _ _ sourceIffExists => sourceIffExists

/-- Substitute scoped evidence through every part of an exactness certificate. -/
def Certificate.replaceFVars (certificate : Certificate)
    (oldVars newVars : Array Expr) : Certificate :=
  let replace := fun expression : Expr => expression.replaceFVars oldVars newVars
  match certificate with
  | .exact lift => .exact (replace lift)
  | .contextual auxiliary target sourceIffExists =>
    .contextual (replace auxiliary) (replace target) (replace sourceIffExists)

/-- The uniform auxiliary type of either kind of certificate. -/
def Certificate.auxiliaryType : Certificate → MetaM Expr
  | .exact lift => do whnf (← mkAppM ``Morew.ExactConstraintLift.Auxiliary #[lift])
  | .contextual auxiliary _ _ => whnf auxiliary

/-- The proof-independent target on original and auxiliary coordinates. -/
def Certificate.targetFunction : Certificate → MetaM Expr
  | .exact lift => mkAppM ``Morew.ExactConstraintLift.target #[lift]
  | .contextual _ target _ => pure target

/-- The exact replacement data shared by target-specific planners. -/
structure Result where
  /-- Checked exactness for the complete selected predicate. -/
  certificate : Certificate
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
  { certificate := result.certificate.replaceFVars oldVars newVars
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
  let body ← Expr.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Expr.depends point type) || (← Expr.depends point value) then
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

private partial def hasPlaceholders (expression : Expr) (seen : FVarIdSet := {}) :
    MetaM Bool := do
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

/-- Check exactness against the selected predicate and the current ordered
retained rows. Rechecking here prevents a contextual certificate from being
applied with stale or selected-row assumptions. -/
def Certificate.check (certificate : Certificate) (source : Expr)
    (retained : Array Expr) : MetaM Unit := do
  let expressions := match certificate with
    | .exact lift => #[lift]
    | .contextual auxiliary target sourceIffExists => #[auxiliary, target, sourceIffExists]
  for expression in #[source] ++ retained ++ expressions do
    if ← hasPlaceholders expression then
      throwError "the exact certificate contains unresolved placeholders"
  if ← unresolved source then throwError "unresolved metavariables in the selected predicate"
  let domain ← predicateDomain source
  for row in retained do
    if ← unresolved row then throwError "unresolved metavariables in retained constraints"
    unless ← isDefEq (← predicateDomain row) domain do
      throwError "retained constraint has a different decision domain"
  match certificate with
  | .exact lift => discard <| checkLift source lift
  | .contextual auxiliary target sourceIffExists =>
    for expression in #[auxiliary, target, sourceIffExists] do
      if ← unresolved expression then
        throwError "conditional exact certificate contains unresolved metavariables"
      checkWithKernel expression
    let targetType ← mkArrow domain (← mkArrow auxiliary (mkSort .zero))
    unless ← isDefEq (← inferType target) targetType do
      throwError "conditional exact target does not have the original domain and uniform auxiliary type"
    let expected ← withLocalDeclD `point domain fun point => do
      let remainder := Decomposition.conjunction (retained.toList.map (mkApp · point))
      let existence ← mkAppM ``Exists #[mkApp target point]
      let iff := mkApp2 (mkConst ``Iff) (mkApp source point) existence
      mkForallFVars #[point] (← mkArrow remainder iff)
    unless ← isDefEq (← inferType sourceIffExists) expected do
      throwError "conditional exact certificate does not match the selected row and retained constraints"

/-- Close a pointwise match without letting retained proofs enter its target
or auxiliary type. Independent exactness keeps the unconditional fast path. -/
def closeCertificate (source point evidence auxiliary target sourceIff : Expr) :
    MetaM Certificate := do
  let auxiliary ← instantiateMVars auxiliary
  let target ← instantiateMVars target
  let sourceIff ← instantiateMVars sourceIff
  for expression in #[source, auxiliary, target, sourceIff] do
    if ← unresolved expression then
      throwError "exact replacement contains unresolved metavariables"
    if ← hasPlaceholders expression then
      throwError "the exact certificate contains unresolved placeholders"
  if ← Expr.depends point auxiliary then
    throwError "the auxiliary type depends on a decision variable"
  if ← Expr.depends evidence auxiliary then
    throwError "the auxiliary type depends on retained feasibility evidence"
  if ← Expr.depends evidence target then
    throwError "generated rows depend on retained feasibility evidence"
  unless ← isDefEq (← inferType point) (← predicateDomain source) do
    throwError "the exact replacement point has a different decision domain"
  unless ← isDefEq (← inferType target) (← mkArrow auxiliary (mkSort .zero)) do
    throwError "the exact replacement target has a different auxiliary type"
  let existence ← mkAppM ``Exists #[target]
  let expected := mkApp2 (mkConst ``Iff) (mkApp source point) existence
  unless ← isDefEq (← inferType sourceIff) expected do
    throwError "the exact certificate does not describe the entire selected predicate"
  checkWithKernel sourceIff
  let closedTarget ← mkLambdaFVars #[point] target
  if !(← Expr.depends evidence sourceIff) then
    let pointwise ← mkLambdaFVars #[point] sourceIff
    let lift ← mkAppM ``Morew.ExactConstraintLift.mk #[auxiliary, closedTarget, pointwise]
    return .exact (← checkLift source lift)
  let conditional ← mkLambdaFVars #[point, evidence] sourceIff
  checkWithKernel conditional
  return .contextual auxiliary closedTarget conditional

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
  let auxiliary ← result.certificate.auxiliaryType
  let targetFunction ← result.certificate.targetFunction
  for expression in #[auxiliary, targetFunction, result.nextDomain, result.targetIff] ++
      result.auxiliary?.toArray ++ result.rowPredicates do
    if ← unresolved expression then throwError "exact replacement contains unresolved metavariables"
    if ← hasPlaceholders expression then
      throwError "the exact replacement contains unresolved placeholders"
  let targetType ← whnf (← inferType targetFunction)
  let .forallE _ domain _ _ := targetType
    | throwError "the exact target is not a function on the original decision domain"
  unless ← isDefEq targetType (← mkArrow domain (← mkArrow auxiliary (mkSort .zero))) do
    throwError "the exact target does not have a uniform auxiliary type"
  let nextDomain ← match result.auxiliary? with
    | none =>
      unless ← isDefEq auxiliary (mkConst ``Unit) do
        throwError "the exact replacement omitted its auxiliary coordinates"
      pure domain
    | some supplied =>
      unless ← isDefEq supplied auxiliary do
        throwError "the exact replacement has a different auxiliary type"
      if ← isDefEq auxiliary (mkConst ``Unit) then
        throwError "Unit auxiliaries must not introduce decision coordinates"
      mkAppM ``Prod #[domain, auxiliary]
  unless ← isDefEq result.nextDomain nextDomain do
    throwError "the exact replacement has a different decision domain"
  for row in result.rowPredicates do
    unless ← isDefEq (← predicateDomain row) nextDomain do
      throwError "a generated row has a different decision domain"
  let expected ← withLocalDeclD `point nextDomain fun point => do
    let target := match result.auxiliary? with
      | none => mkApp2 targetFunction point (mkConst ``Unit.unit)
      | some _ => mkApp2 targetFunction (.proj ``Prod 0 point) (.proj ``Prod 1 point)
    let rows := result.rowPredicates.toList.map (mkApp · point)
    mkForallFVars #[point]
      (mkApp2 (mkConst ``Iff) target (Decomposition.conjunction rows))
  unless ← isDefEq (← inferType result.targetIff) expected do
    throwError mismatchMessage
  checkWithKernel result.targetIff

/-- Validate both exactness under the current retained context and the complete
decision layout and ordered target decomposition. -/
def Result.check (result : Result) (source : Expr) (retained : Array Expr) : MetaM Unit := do
  result.certificate.check source retained
  result.checkTargetIff

end Morew.Elab.Rewrite.Plan
