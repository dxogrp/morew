/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.QuadConic.Objective
import Morew.Elab.Cone.Rows
import Morew.Elab.Cone.Finite
import Morew.Elab.Expr
import Morew.Elab.State

/-! Construct `QuadConic.Form` with exact objective equality and feasibility equivalence.
Function spaces with abstract indices require `Finite` evidence for the index type. -/

namespace Morew.Elab.QuadConic

open Lean Lean.Meta
open Morew.Elab.Rewrite
open Reformulation
open Morew.Elab.Cone (RowResult)

private def buildFormCore (presentation : PresentationState) (objective? : Option ObjectiveResult)
    (provider : Affine.EvidenceProvider)
    (certifiedRows : Array (Option (Array RowResult))) :
    MetaM (Except Expr.Error Expr) := do
  for expression in #[presentation.domainType, presentation.valueType, presentation.objective] ++
      presentation.binders.map (·.type) ++ presentation.constraints.map (·.predicate) do
    if ← Morew.Elab.Rewrite.Plan.unresolved expression then
      return .error {
        expression
        reason := ← addMessageContext "quadratic conic form: unresolved metavariables in typed presentation"
      }
  unless certifiedRows.isEmpty || certifiedRows.size == presentation.constraints.size do
    throwError "cached row entry count does not match the typed presentation"
  let canonical ← presentation.canonicalProblem
  let objectiveResult ← match objective? with
    | some objective => validateObjectiveResult presentation objective
    | none => reifyObjective presentation provider
  let objective ← match objectiveResult with
    | .error error => return .error error
    | .ok result => pure result
  let rows ← match ← Morew.Elab.Cone.buildRows presentation provider certifiedRows with
    | .error error => return .error error
    | .ok result => pure result
  let form ← Morew.Elab.Cone.Space.withCanonicalDomain presentation.domainType do
    let sense := mkConst <| match presentation.sense with
      | .minimize => ``Morew.ObjectiveSense.minimize
      | .maximize => ``Morew.ObjectiveSense.maximize
    let data ← mkAppM ``Morew.QuadConic.Data.mk
      #[sense, objective.quadratic, objective.affine, objective.curvature,
        mkNatLit rows.count, rows.constraints]
    let represented ← mkAppM ``Morew.QuadConic.Data.toProblem #[data]
    let equality ← mkAppM ``Morew.Problem.ext
      #[represented, canonical, objective.pointwiseEquality, rows.feasibleIff]
    let form ← instantiateMVars (← mkAppM ``Morew.QuadConic.Form.mk #[data, equality])
    let expected ← mkAppM ``Morew.QuadConic.Form #[canonical]
    unless ← isDefEq (← inferType form) expected do
      throwError "quadratic conic form does not represent the current canonical problem"
    if form.hasMVar then
      throwError "quadratic conic form contains unresolved metavariables"
    checkWithKernel form
    return form
  -- Expose domain aliases in canonical instance types so persisted forms support field notation.
  let domain ← Morew.Elab.Cone.Space.structuralDomain presentation.domainType
  let publicType ← Morew.Elab.Cone.Space.withCanonicalDomain domain do
    mkAppOptM ``Morew.QuadConic.Form #[some domain, none, none, none, some canonical]
  let form ← mkAppOptM ``id #[some publicType, some form]
  checkWithKernel form
  return .ok form

private def buildFormWith (presentation : PresentationState) (objective? : Option ObjectiveResult)
    (provider : Affine.EvidenceProvider) (certifiedRows : Array (Option (Array RowResult))) :
    MetaM (Except Expr.Error Expr) :=
  State.withIsolatedMVars do
    try
      Morew.Elab.Cone.Finite.withPresentationFiniteInstances
        (fun result oldVars newVars => result.replaceFVars oldVars newVars)
        presentation (buildFormCore presentation objective? provider certifiedRows)
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"quadratic conic form: {error.toMessageData}"
      }

/-- Certify the current presentation using explicit objective fields.
Check the objective against the current domain, canonical instances, and declared direction;
validate cached rows against the current predicates. -/
def buildFormWithObjective (presentation : PresentationState) (objective : ObjectiveResult)
    (provider : Affine.EvidenceProvider := {})
    (certifiedRows : Array (Option (Array RowResult)) := #[]) :
    MetaM (Except Expr.Error Expr) :=
  buildFormWith presentation (some objective) provider certifiedRows

/-- Certify `presentation.canonicalProblem`, retaining objective sense and row order.
`True` contributes no rows. A nonempty cache has one slot per presentation entry:
`some` supplies rows in decomposed order; `none` normalizes the entry.
Cached proofs are checked against the current predicates. -/
def buildForm (presentation : PresentationState) (provider : Affine.EvidenceProvider := {})
    (certifiedRows : Array (Option (Array RowResult)) := #[]) :
    MetaM (Except Expr.Error Expr) :=
  buildFormWith presentation none provider certifiedRows

end Morew.Elab.QuadConic
