/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Elab.Expr
import Morew.Elab.Rewrite.Decomposition

/-! Shared exact replacement data, scoped evidence, and ordered target equivalence.
Conic and NLP planners provide target reduction, space checks, and row certification. -/

namespace Morew.Elab.Rewrite.Plan

open Lean Lean.Meta

/-- Unconditional exactness or exactness under retained constraints.
Auxiliary types are uniform and targets are independent of feasibility proofs. -/
inductive Certificate where
  | exact (repr : Expr)
  | contextual (auxiliary target sourceIffExists : Expr)

/-- The proof-bearing expression shared when storing a replacement. -/
def Certificate.expression : Certificate → Expr
  | .exact repr => repr
  | .contextual _ _ sourceIffExists => sourceIffExists

/-- Substitute scoped evidence through every part of an exactness certificate. -/
def Certificate.replaceFVars (certificate : Certificate)
    (oldVars newVars : Array Expr) : Certificate :=
  let replace := fun expression : Expr => expression.replaceFVars oldVars newVars
  match certificate with
  | .exact repr => .exact (replace repr)
  | .contextual auxiliary target sourceIffExists =>
    .contextual (replace auxiliary) (replace target) (replace sourceIffExists)

/-- The uniform auxiliary type of either kind of certificate. -/
def Certificate.auxiliaryType : Certificate → MetaM Expr
  | .exact repr => do whnf (← mkAppM ``Morew.ConstraintRepr.Auxiliary #[repr])
  | .contextual auxiliary _ _ => whnf auxiliary

/-- The proof-independent target on original and auxiliary coordinates. -/
def Certificate.targetFunction : Certificate → MetaM Expr
  | .exact repr => mkAppM ``Morew.ConstraintRepr.target #[repr]
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
  /-- The instantiated representation target is equivalent to the row conjunction. -/
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

-- Keep caller metavariables in local declarations unassigned.
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

/-- Check that a record describes the complete selected predicate. -/
def checkRepr (source repr : Expr) : MetaM Expr := do
  let type ← whnf (← inferType repr)
  unless type.isAppOfArity ``Morew.ConstraintRepr 2 do
    throwError "expected a constraint representation"
  unless ← isDefEq type.getAppArgs[1]! source do
    throwError "the supplied exact certificate does not describe the entire selected predicate"
  let repr ← instantiateMVars repr
  if ← unresolved repr then
    throwError "the exact certificate contains unresolved metavariables; supply its input and bound maps explicitly"
  checkWithKernel repr
  return repr

/-- Check exactness against the selected predicate and current ordered retained rows. -/
def Certificate.check (certificate : Certificate) (source : Expr)
    (retained : Array Expr) : MetaM Unit := do
  let expressions := match certificate with
    | .exact repr => #[repr]
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
  | .exact repr => discard <| checkRepr source repr
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

/-- Close a pointwise match with auxiliary types and targets independent of retained proofs. -/
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
    throwError "the auxiliary type depends on an optimization variable"
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
    let repr ← mkAppM ``Morew.ConstraintRepr.mk #[auxiliary, closedTarget, pointwise]
    return .exact (← checkRepr source repr)
  let conditional ← mkLambdaFVars #[point, evidence] sourceIff
  checkWithKernel conditional
  return .contextual auxiliary closedTarget conditional

private def adaptRepr (source domain rule : Expr) (adapter : Name)
    (inputType outputType : Expr) : MetaM Expr := do
  let input ← mkFreshExprMVar (← mkArrow domain inputType)
  let output ← mkFreshExprMVar (← mkArrow domain outputType)
  let repr ← mkAppM adapter #[rule, input, output]
  checkRepr source repr

/-- Adapt one of the supported exact representation records to a selected predicate. -/
def customRepr (source domain rule : Expr) : MetaM Expr := do
  let type ← whnf (← inferType rule)
  let args := type.getAppArgs
  if type.isAppOfArity ``Morew.ConstraintRepr 2 then
    return ← checkRepr source rule
  if type.isAppOfArity ``Morew.GraphRepr 3 then
    let saved ← saveState
    try
      return ← adaptRepr source domain rule
        ``Morew.GraphRepr.toConstraintRepr args[0]! args[1]!
    catch _ =>
      saved.restore
      return ← adaptRepr source domain rule
        ``Morew.GraphRepr.toConstraintReprSymm args[0]! args[1]!
  if type.isAppOfArity ``Morew.EpigraphRepr 4 then
    return ← adaptRepr source domain rule
      ``Morew.EpigraphRepr.toConstraintRepr args[0]! args[1]!
  if type.isAppOfArity ``Morew.HypographRepr 4 then
    return ← adaptRepr source domain rule
      ``Morew.HypographRepr.toConstraintRepr args[0]! args[1]!
  throwError "expected a ConstraintRepr, GraphRepr, EpigraphRepr, or HypographRepr for the entire selected predicate"

/-- Check target equivalence with the supplied decision layout and row order.
Smooth planning checks this before using generated rows as domain evidence. -/
def Result.checkTargetIff (result : Result)
    (mismatchMessage : MessageData :=
      "internal error: target decomposition does not match the constraint representation") : MetaM Unit := do
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
