/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic
import Morew.Elab.Rewrite.Plan

/-!
# Shared exact conic replacement planning

Inspect custom representations, split ordered target rows, and certify each row.
Operation recognizers and the surface runner share this implementation.
-/

namespace Morew.Elab.Conic.Plan

open Lean Lean.Meta
open Morew.Elab.Rewrite Morew.Elab.Rewrite.Plan

/-- A complete exact replacement, before presentation names are allocated. -/
structure Result extends Morew.Elab.Rewrite.Plan.Result where
  /-- Checked affine cone rows corresponding to `rowPredicates`. -/
  certifiedRows : Array RowResult

/-- A same-domain replacement certified under exactly the retained row conjunction. -/
structure ContextualResult where
  /-- The unchanged decision domain. -/
  domain : Expr
  /-- Generated predicates in presentation order. -/
  rowPredicates : Array Expr
  /-- Checked affine cone constraints for all generated predicates. -/
  certifiedRows : Array RowResult
  /-- `∀ x, remainder x → (source x ↔ conjunction rowPredicates x)`. -/
  conditionalIff : Expr

/-- Rebase a contextual replacement, including its retained domain evidence. -/
def ContextualResult.replaceFVars (result : ContextualResult)
    (oldVars newVars : Array Expr) : ContextualResult := {
  domain := result.domain.replaceFVars oldVars newVars
  rowPredicates := result.rowPredicates.map (·.replaceFVars oldVars newVars)
  certifiedRows := result.certifiedRows.map fun row => {
    constraint := row.constraint.replaceFVars oldVars newVars
    pointwiseIff := row.pointwiseIff.replaceFVars oldVars newVars }
  conditionalIff := result.conditionalIff.replaceFVars oldVars newVars
}

/-- Either an unconditional exact lift or a replacement using retained evidence. -/
abbrev Prepared := Sum Result ContextualResult

/-- Rebase all expressions of an unconditional replacement. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result :=
  let replace := fun expression : Expr => expression.replaceFVars oldVars newVars
  { toResult := result.toResult.replaceFVars oldVars newVars
    certifiedRows := result.certifiedRows.map fun row => {
      constraint := replace row.constraint
      pointwiseIff := replace row.pointwiseIff } }

/-- Rebase either kind of checked replacement. -/
def Prepared.replaceFVars (result : Prepared) (oldVars newVars : Array Expr) : Prepared :=
  match result with
  | .inl exact => .inl (exact.replaceFVars oldVars newVars)
  | .inr contextual => .inr (contextual.replaceFVars oldVars newVars)

/-- Retry a failed certificate with safe finite evidence exposed by helpers.
Direct recognition keeps its original fast path; speculative declarations and
metavariables are discarded before retrying the unchanged source predicates. -/
def withHelperFiniteInstances {α : Type}
    (replace : α → Array Expr → Array Expr → α)
    (sources : Array Expr)
    (action : MetaM (Except Affine.AffineError α)) :
    MetaM (Except Affine.AffineError α) := Affine.withIsolatedMVars do
  let failure (error : Exception) : MetaM (Except Affine.AffineError α) := do
    return Except.error ({
      expression := sources[0]?.getD (mkConst ``True)
      reason := ← addMessageContext error.toMessageData } : Affine.AffineError)
  try
    let replaceResult := fun result oldVars newVars =>
      result.map (fun value => replace value oldVars newVars)
    let direct ← Affine.withIsolatedMVars do
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
    (action : MetaM (Except Affine.AffineError α)) :
    MetaM (Except Affine.AffineError α) := do
  let mut instances := #[]
  let sources := #[presentation.objective] ++ presentation.constraints.map (·.predicate)
  for source in sources do
    for inst in ← Affine.sourceFiniteInstances source do
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

private abbrev conjunction := Decomposition.conjunction

-- Adapters can leave another representation's target projection at the head.
-- Expose only these record fields, stopping before arbitrary predicate helpers
-- or arithmetic operands are unfolded.
/-- Reduce checked representation target fields without unfolding predicate helpers. -/
partial def exposeTarget (body : Expr) : MetaM Expr := do
  let body ← Affine.reduceStructure body (preserveLets := true)
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

private def finishCore (source domain lift : Expr) (provider : Affine.EvidenceProvider) : MetaM Result := do
  let auxiliary ← whnf (← mkAppM ``Morew.ExactConstraintLift.Auxiliary #[lift])
  let noAuxiliary ← isDefEq auxiliary (mkConst ``Unit)
  let auxiliary? := if noAuxiliary then none else some auxiliary
  let nextDomain ← if noAuxiliary then pure domain else mkAppM ``Prod #[domain, auxiliary]
  unless ← Affine.isSupportedSpace nextDomain do
    throwError "unsupported exact-lift decision space {nextDomain}; expected real scalars, products, or finite function spaces"
  let targetFunction ← whnf (← mkAppM ``Morew.ExactConstraintLift.target #[lift])
  let (rowPredicates, targetIff) ← withLocalDeclD `point nextDomain fun point => do
    let target := if noAuxiliary then mkApp2 targetFunction point (mkConst ``Unit.unit)
      else mkApp2 targetFunction (.proj ``Prod 0 point) (.proj ``Prod 1 point)
    let (bodies, proof) ← splitTarget target
    let rows ← bodies.toArray.mapM fun body => mkLambdaFVars #[point] body
    return (rows, ← mkLambdaFVars #[point] proof)
  let certifiedRows ← certifyRows rowPredicates provider
  let prepared : Morew.Elab.Rewrite.Plan.Result := {
    lift, auxiliary?, nextDomain, rowPredicates, targetIff }
  prepared.checkTargetIff
  let _ ← checkLift source lift
  return { toResult := prepared, certifiedRows }

/-- Split and certify every row of an exact lift. -/
def finish (source domain lift : Expr) (provider : Affine.EvidenceProvider) : MetaM Result := do
  let target ← whnf (← mkAppM ``Morew.ExactConstraintLift.target #[lift])
  let result ← withHelperFiniteInstances Result.replaceFVars #[target] do
    let result ← withFiniteInstances (← Affine.sourceFiniteInstances target).toList do
      finishCore source domain lift provider
    return .ok result
  match result with
  | .ok result => return result
  | .error error => throwError error.reason

/-- Discard unused retained assumptions while reusing the already certified rows.
An unconditional same-domain proof becomes an ordinary exact lift; otherwise
the complete conditional proof remains attached to the replacement. -/
def prepareContextual (source : Expr) (retained : Array Expr)
    (result : ContextualResult) : MetaM Prepared := do
  let exact? ← withLocalDeclD `point result.domain fun point => do
    let remainder := conjunction (retained.toList.map (mkApp · point))
    withLocalDeclD `retained remainder fun evidence => do
      let proof := (mkApp2 result.conditionalIff point evidence).headBeta
      if ← Affine.depends evidence proof then return none
      let targetBody := conjunction (result.rowPredicates.toList.map (mkApp · point))
      let target ← mkLambdaFVars #[point] targetBody
      let pointwise ← mkLambdaFVars #[point] proof
      let lift ← instantiateMVars (← mkAppM ``Morew.ExactConstraintLift.ofIff
        #[target, pointwise])
      let lift ← checkLift source lift
      let targetIff ← mkLambdaFVars #[point] (mkApp (mkConst ``Iff.rfl) targetBody)
      checkWithKernel targetIff
      return some ({
        lift
        auxiliary? := none
        nextDomain := result.domain
        rowPredicates := result.rowPredicates
        targetIff
        certifiedRows := result.certifiedRows
      } : Result)
  return match exact? with
    | some exact => .inl exact
    | none => .inr result

/-- Plan one entire selected predicate. A supplied record bypasses automatic
operation matching, but every resulting row still undergoes affine checking.
Caller metavariables and the environment are restored on failure. -/
private def planDirect (automaticLift : Expr → Expr → MetaM Expr)
    (sourcePredicate : Expr) (rule? : Option Expr := none)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError Result) :=
  Affine.withIsolatedMVars do
    try
      let source ← instantiateMVars sourcePredicate
      if ← unresolved source then throwError "unresolved metavariables in the selected predicate"
      let domain ← predicateDomain source
      let result ← withFiniteInstances (← Affine.sourceFiniteInstances source).toList do
        withLocalDeclD `point domain fun point =>
          withPredicateEvidence point (mkApp source point) do
            let lift ← match rule? with
              | none => automaticLift source domain
              | some rule => customLift source domain (← instantiateMVars rule)
            finish source domain lift provider
      return .ok result
    catch error =>
      return .error {
        expression := sourcePredicate
        reason := ← addMessageContext error.toMessageData
      }

/-- Certify a selected predicate, exposing finite evidence from helpers only if
the direct attempt fails. Matching always uses the original predicate. -/
def plan (automaticLift : Expr → Expr → MetaM Expr) (sourcePredicate : Expr)
    (rule? : Option Expr := none) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Affine.AffineError Result) :=
  Affine.withIsolatedMVars do
    withHelperFiniteInstances Result.replaceFVars #[sourcePredicate]
      (planDirect automaticLift sourcePredicate rule? provider)

end Morew.Elab.Conic.Plan
