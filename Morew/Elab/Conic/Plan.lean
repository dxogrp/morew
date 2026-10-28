/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic
import Morew.Elab.Rewrite.Plan
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Shared exact conic replacement planning

Adapt explicit representations, split ordered target rows, and certify each row.
Registered-rule selection and explicit certificates share these finishing checks.
-/

namespace Morew.Elab.Conic.Plan

open Lean Lean.Meta
open Morew.Elab.Rewrite Morew.Elab.Rewrite.Plan

/-- A complete exact replacement, before presentation names are allocated. -/
structure Result extends Morew.Elab.Rewrite.Plan.Result where
  /-- Checked affine cone rows corresponding to `rowPredicates`. -/
  certifiedRows : Array RowResult

/-- Rebase all expressions of a checked replacement. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result :=
  let replace := fun expression : Expr => expression.replaceFVars oldVars newVars
  { toResult := result.toResult.replaceFVars oldVars newVars
    certifiedRows := result.certifiedRows.map fun row => {
      constraint := replace row.constraint
      pointwiseIff := replace row.pointwiseIff } }

/-- Retry a failed certificate with safe finite evidence exposed by helpers.
Direct recognition keeps its original fast path; speculative declarations and
metavariables are discarded before retrying the unchanged source predicates. -/
def withHelperFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (sources : Array Expr)
    (action : MetaM (Except Expr.Error α)) :
    MetaM (Except Expr.Error α) := State.withIsolatedMVars do
  let failure (error : Exception) : MetaM (Except Expr.Error α) := do
    return Except.error ({
      expression := sources[0]?.getD (mkConst ``True)
      reason := ← addMessageContext error.toMessageData } : Expr.Error)
  try
    let replaceResult := fun result oldVars newVars =>
      result.map (fun value => replace value oldVars newVars)
    let direct ← State.withIsolatedMVars do
      try action catch error => failure error
    if let .ok result := direct then return .ok result
    let mut additional := #[]
    for source in sources do
      for inst in ← Affine.helperFiniteInstances source do
        unless additional.contains inst do
          additional := additional.push inst
    if additional.isEmpty then return direct
    withScopedFiniteInstances replaceResult additional.toList action
  catch error => failure error

/-- Retain finite-index evidence from the entire presentation while constructing
certificates. A row can carry the only explicit indexing instance needed by the
objective or another row. Duplicate proofs are scoped once, and all temporary
bindings are substituted through the completed result before leaving scope. -/
def withPresentationFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (presentation : Reformulation.PresentationState)
    (action : MetaM (Except Expr.Error α)) :
    MetaM (Except Expr.Error α) := do
  let mut instances := #[]
  let sources := #[presentation.objective] ++ presentation.constraints.map (·.predicate)
  for source in sources do
    for inst in ← Expr.sourceFiniteInstances source do
      unless instances.contains inst do
        instances := instances.push inst
  withHelperFiniteInstances replace sources do
    withScopedFiniteInstances
      (fun result oldVars newVars => result.map (fun value => replace value oldVars newVars))
      instances.toList action

/-- Retain source indexing evidence while constructing an exact lift. -/
def withFiniteInstances (instances : List Expr) (action : MetaM Result) :
    MetaM Result :=
  withScopedFiniteInstances Result.replaceFVars instances action

/-- Retain independent source lets while constructing an exact lift. -/
def withPredicateEvidence (point body : Expr)
    (action : MetaM Result) : MetaM Result :=
  withScopedEvidence Result.replaceFVars point body action

-- Adapters can leave another representation's target projection at the head.
-- Expose only these record fields, stopping before arbitrary predicate helpers
-- or arithmetic operands are unfolded.
/-- Reduce checked representation target fields without unfolding predicate helpers. -/
partial def exposeTarget (body : Expr) : MetaM Expr := do
  let body ← Expr.reduceStructure body (preserveLets := true)
  let head := body.getAppFn
  let prefixSize? := match head.constName? with
    | some ``Morew.ExactConstraintLift.target => some 3
    | some ``Morew.GraphRepresentation.target => some 4
    | some ``Morew.EpigraphRepresentation.target => some 5
    | some ``Morew.HypographRepresentation.target => some 5
    | _ => none
  if let some prefixSize := prefixSize? then
    let args := body.getAppArgs
    if args.size >= prefixSize then
      let partialTarget := mkAppN head (args.extract 0 prefixSize)
      let reduced ← whnf partialTarget
      unless reduced == partialTarget do
        return ← exposeTarget (mkAppN reduced (args.extract prefixSize args.size))
  return body

/-- Expose representation fields and split a checked replacement target. -/
def splitTarget (body : Expr) : MetaM (List Expr × Expr) :=
  Decomposition.split body fun body => do
    let body ← exposeTarget body
    -- Keep exact-lift diagnostics stable while sharing conjunction proof assembly.
    unless body.isLet || body.isConstOf ``True || body.isAppOfArity ``And 2 ||
        body.isForall || body.isAppOfArity ``Eq 3 || body.isAppOfArity ``LE.le 4 ||
        body.isAppOfArity ``GE.ge 4 || body.isAppOfArity ``Membership.mem 5 do
      throwError "unsupported exact target predicate {body}; expected True, conjunctions, affine equalities and non-strict inequalities, supported cone memberships, or a finite exponential membership family"
    return body

/-- Certify each replacement row without changing its presentation predicate. -/
def certifyRows (predicates : Array Expr) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Array RowResult) := do
  predicates.mapM fun predicate => do
    match ← normalizeRow predicate provider with
    | .ok row => pure row
    | .error error => throwError "generated row: {error.reason}"

private def finishCore (source domain : Expr) (certificate : Certificate)
    (retained : Array Expr) (provider : Affine.EvidenceProvider) : MetaM Result := do
  certificate.check source retained
  let auxiliary ← whnf (← certificate.auxiliaryType)
  let noAuxiliary ← isDefEq auxiliary (mkConst ``Unit)
  let auxiliary? := if noAuxiliary then none else some auxiliary
  let nextDomain ← if noAuxiliary then pure domain else mkAppM ``Prod #[domain, auxiliary]
  unless ← Expr.isSupportedSpace nextDomain do
    throwError "unsupported exact-lift decision space {nextDomain}; expected real scalars, products, or finite function spaces"
  let targetFunction ← whnf (← certificate.targetFunction)
  let (rowPredicates, targetIff) ← withLocalDeclD `point nextDomain fun point => do
    let target := if noAuxiliary then mkApp2 targetFunction point (mkConst ``Unit.unit)
      else mkApp2 targetFunction (.proj ``Prod 0 point) (.proj ``Prod 1 point)
    let (bodies, proof) ← splitTarget target
    let rows ← bodies.toArray.mapM fun body => mkLambdaFVars #[point] body
    return (rows, ← mkLambdaFVars #[point] proof)
  let prepared : Morew.Elab.Rewrite.Plan.Result := {
    certificate, auxiliary?, nextDomain, rowPredicates, targetIff }
  prepared.check source retained
  let certifiedRows ← certifyRows rowPredicates provider
  return { toResult := prepared, certifiedRows }

/-- Split and certify every row of an exact lift. -/
def finish (source domain : Expr) (certificate : Certificate)
    (retained : Array Expr) (provider : Affine.EvidenceProvider) : MetaM Result := do
  let target ← whnf (← certificate.targetFunction)
  let result ← withHelperFiniteInstances Result.replaceFVars #[target] do
    let result ← withFiniteInstances (← Expr.sourceFiniteInstances target).toList do
      finishCore source domain certificate retained provider
    return .ok result
  match result with
  | .ok result => return result
  | .error error => throwError error.reason

/-- Adapt an explicit record for the entire selected predicate and certify its rows.
Caller metavariables and the environment are restored on failure. -/
private def planDirect (sourcePredicate rule : Expr)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Result) :=
  State.withIsolatedMVars do
    try
      let source ← instantiateMVars sourcePredicate
      if ← unresolved source then throwError "unresolved metavariables in the selected predicate"
      let domain ← predicateDomain source
      let result ← withFiniteInstances (← Expr.sourceFiniteInstances source).toList do
        withLocalDeclD `point domain fun point =>
          withPredicateEvidence point (mkApp source point) do
            let lift ← customLift source domain rule
            finish source domain (.exact lift) #[] provider
      return .ok result
    catch error =>
      return .error {
        expression := sourcePredicate
        reason := ← addMessageContext error.toMessageData
      }

/-- Certify an explicit record, exposing finite evidence from helpers only if
the direct attempt fails. Adaptation always uses the original predicate. -/
def plan (sourcePredicate rule : Expr) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Expr.Error Result) :=
  State.withIsolatedMVars do
    withHelperFiniteInstances Result.replaceFVars #[sourcePredicate]
      (planDirect sourcePredicate rule provider)

end Morew.Elab.Conic.Plan
