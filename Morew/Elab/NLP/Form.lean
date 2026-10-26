/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Rows
import Morew.Elab.Reformulation.Presentation

/-!
# Complete checked smooth-NLP forms

`buildForm` certifies every displayed row and the unchanged objective on a common
open domain. Comparisons are normalized only in the stored data; predicates and
their presentation groups remain unchanged. Symbolic finite families contribute
symbolic counts, with their coordinates in increasing order.

Optional cached blocks retain evidence already checked while planning exact
rewrites. Each cache entry must represent precisely its current predicate and
prove inclusion of the current feasibility, including any auxiliary variables.
The builder checks all cached terms and exact representation equality with the
kernel. No condition is added to feasibility and no convexity is required.
-/

namespace Morew.Elab.NLP

open Lean Lean.Meta Qq
open Reformulation

-- Stored forms expose structural types, so ordinary field notation can synthesize
-- the same canonical structures for Matrix and finite-index aliases.
private partial def structuralDomain (type : Expr) : MetaM Expr := do
  let shape ← whnf type
  if shape.isConstOf ``Real then return shape
  if let some size ← Affine.Space.euclideanDimension? shape then
    let size : Q(Nat) := size
    return q(EuclideanSpace ℝ (Fin $size))
  if shape.isAppOfArity ``Prod 2 then
    return ← mkAppM ``Prod #[← structuralDomain shape.getAppArgs[0]!,
      ← structuralDomain shape.getAppArgs[1]!]
  if let .forallE _ index target _ := shape then
    let index ← whnf index
    let target ← Core.betaReduce (← whnf target)
    if target.hasLooseBVars then throwError "NLP rows require a nondependent finite space"
    return ← mkArrow index (← structuralDomain target)
  throwError "unsupported smooth decision space {type}"

private def formError (expression : Expr) (reason : MessageData)
    (kind : Smooth.SmoothFailureKind := .invalidInstance) : MetaM Domain.DomainError := do
  return {
    source := expression, expression, type := ← inferType expression, kind
    reason := ← addMessageContext m!"NLP form: {reason}"
  }

-- Cached blocks are data as well as proofs: check their completeness and their
-- exact predicates before projecting the stored finite table.
private def checkCached (decision feasible predicate : Expr) (result : Rows.Result) :
    MetaM Rows.Result := do
  unless result.rowCertificates.size == 1 && result.rowBlocks.size == 1 do
    throwError "cached NLP entry must certify exactly one presentation predicate"
  for expression in result.rowCertificates ++ result.rowBlocks ++
      #[result.domain, result.domainIsOpen, result.feasibleMemDomain] do
    unless ← Domain.Evidence.complete expression do
      throwError "cached NLP entry contains unresolved terms or placeholders"
    checkWithKernel expression
  let expectedOpen ← Space.withCanonicalSpaces #[decision] <|
    mkAppM ``IsOpen #[result.domain]
  unless ← isDefEq (← inferType result.domainIsOpen) expectedOpen do
    throwError "cached NLP entry changed its open evaluation domain"
  let expectedInclusion ← withLocalDeclD `point decision fun point => do
    let membership ← mkAppM ``Membership.mem #[result.domain, point]
    mkForallFVars #[point] (← mkArrow (mkApp feasible point) membership)
  unless ← isDefEq (← inferType result.feasibleMemDomain) expectedInclusion do
    throwError "cached NLP entry does not cover current feasibility"
  let expectedProof ← Space.withCanonicalSpaces #[decision] <|
    mkAppM ``Morew.NLP.Rows.Certified #[result.domain, predicate]
  unless ← isDefEq (← inferType result.rowCertificates[0]!) expectedProof do
    throwError "cached NLP entry changed the presentation predicate"
  let expectedBlock ← Space.withCanonicalSpaces #[decision] <|
    mkAppM ``Morew.NLP.Rows.Block #[result.domain, predicate]
  unless ← isDefEq (← inferType result.rowBlocks[0]!) expectedBlock do
    throwError "cached NLP row data changed the presentation predicate"
  return result

private def buildFormCore (presentation : PresentationState)
    (cached : Array (Option Rows.Result)) : MetaM (Except Domain.DomainError Expr) := do
  for expression in #[presentation.domainType, presentation.valueType, presentation.objective] ++
      presentation.binders.map (·.type) ++ presentation.constraints.map (·.predicate) do
    unless ← Domain.Evidence.complete expression do
      return .error (← formError expression
        "typed presentation contains unresolved expressions or placeholders" .unresolved)
  unless cached.isEmpty || cached.size == presentation.constraints.size do
    throwError "cached NLP entry count does not match the typed presentation"
  unless (← whnf presentation.valueType).isConstOf ``Real do
    return .error (← formError presentation.objective "expected a real-valued objective")
  let canonical ← presentation.canonicalProblem
  let feasible ← mkAppM ``Morew.Problem.feasible #[canonical]
  let mut certificates := #[]
  -- Admission covers every final predicate before whole-objective certification.
  for index in [:presentation.constraints.size] do
    let entry := presentation.constraints[index]!
    let outcome ← match (cached[index]?).getD none with
      | some result => do
        try pure (.ok (← checkCached presentation.domainType feasible entry.predicate result))
        catch exception => pure (.error (← formError entry.predicate exception.toMessageData))
      | none => Rows.certifyRows feasible #[entry.predicate]
    match outcome with
    | .error error => return .error { error with
        rowIndex? := some index
        reason := ← addMessageContext m!"constraint `{entry.name}`: {error.reason}" }
    | .ok result => certificates := certificates.push result
  -- Fix only the analytic codomain spelling. The projection is definitionally
  -- the original objective, including on OrderDual-valued maximizing problems.
  -- No analytic instances are installed on OrderDual itself.
  let realObjective ← mkAppOptM ``Morew.Problem.objective
    #[some presentation.domainType, some q(ℝ), some canonical]
  let objective ← Domain.certifyWithEvidence feasible #[realObjective] Rows.factsProvider
  let .ok objective := objective | do
    let .error error := objective | unreachable!
    return .error { error with
      source := presentation.objective
      reason := ← addMessageContext m!"objective: {error.reason}" }
  let mut domain := objective.domain
  let mut opened := objective.domainIsOpen
  let mut included := objective.feasibleMemDomain
  let mut smooth := objective.smooth[0]!
  let mut blocks := #[]
  for certificate in certificates do
    let next ← mkAppM ``Morew.NLP.Domain.inter #[domain, certificate.domain]
    let left ← mkAppM ``Morew.NLP.Domain.inter_left #[domain, certificate.domain]
    let right ← mkAppM ``Morew.NLP.Domain.inter_right #[domain, certificate.domain]
    smooth ← Space.withCanonicalSpaces #[presentation.domainType] <|
      mkAppM ``ContDiffOn.mono #[smooth, left]
    blocks ← blocks.mapM fun block => Space.withCanonicalSpaces #[presentation.domainType] <|
      mkAppM ``Morew.NLP.Rows.Block.mono #[block, left]
    blocks := blocks.push (← Space.withCanonicalSpaces #[presentation.domainType] <|
      mkAppM ``Morew.NLP.Rows.Block.mono #[certificate.rowBlocks[0]!, right])
    opened ← Space.withCanonicalSpaces #[presentation.domainType] <|
      mkAppM ``Morew.NLP.Domain.inter_open
        #[domain, certificate.domain, opened, certificate.domainIsOpen]
    included ← mkAppM ``Morew.NLP.Domain.inter_includes
      #[feasible, domain, certificate.domain, included, certificate.feasibleMemDomain]
    domain := next
  let form ← Space.withCanonicalSpaces #[presentation.domainType] do
    let block ← if blocks.isEmpty then
        mkAppM ``Morew.NLP.Rows.Block.truth #[domain]
      else do
        let mut block := blocks.back!
        for left in blocks.toList.reverse.tail do
          block ← mkAppM ``Morew.NLP.Rows.Block.and #[left, block]
        pure block
    let sense := mkConst <| match presentation.sense with
      | .minimize => ``Morew.ObjectiveSense.minimize
      | .maximize => ``Morew.ObjectiveSense.maximize
    let form ← mkAppM ``Morew.NLP.Rows.Block.toForm
      #[canonical, block, sense, opened, smooth, included]
    let form ← instantiateMVars form
    let expected ← mkAppM ``Morew.NLP.Form #[canonical]
    unless ← isDefEq (← inferType form) expected do
      throwError "NLP form does not represent the complete current problem"
    let data ← mkAppM ``Morew.NLP.Form.data #[form]
    let recordedSense ← mkAppM ``Morew.NLP.Data.sense #[data]
    unless ← isDefEq recordedSense sense do
      throwError "NLP form changed the recorded objective sense"
    unless ← Domain.Evidence.complete form do
      throwError "NLP form contains unresolved expressions or placeholders"
    checkWithKernel form
    return form
  let decision ← structuralDomain presentation.domainType
  -- Nested aliases also occur inside the chosen instance expressions. Rebuild
  -- those expressions over the exposed shape so ordinary projections match them.
  let publicType ← Space.withCanonicalSpaces #[decision] <|
    mkAppOptM ``Morew.NLP.Form #[some decision, none, none, none, some canonical]
  let form ← mkAppOptM ``id #[some publicType, some form]
  checkWithKernel form
  return .ok form

/-- Build concrete smooth-NLP data representing the entire presentation exactly.
The optional cache has one slot per displayed row, each certifying that row and
the current feasibility. Failed and successful attempts leave caller metavariables
unchanged. Objective sense is retained separately from representation equality. -/
def buildForm (presentation : PresentationState) (cached : Array (Option Rows.Result) := #[]) :
    MetaM (Except Domain.DomainError Expr) :=
  Affine.withIsolatedMVars do
    try buildFormCore presentation cached
    catch exception =>
      return .error (← formError presentation.objective exception.toMessageData)

end Morew.Elab.NLP
