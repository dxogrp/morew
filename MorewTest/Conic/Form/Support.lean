/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Form
import MorewTest.ElabSupport
import Morew.Elab.Expr

/-! # Helpers for checking complete conic forms without importing test cases -/

namespace MorewTest.Conic.Form

open Lean Lean.Meta Lean.Elab Lean.Elab.Term
open Morew

def presentationFor (source : Expr) (sense : ObjectiveSense := .minimize)
    (noConstraints : Bool := false) : MetaM Elab.Reformulation.PresentationState := do
  let type ← whnf (← inferType source)
  unless type.isAppOfArity ``Problem 2 do throwError "expected a problem"
  let domain := type.getAppArgs[0]!
  let feasible ← mkAppM ``Problem.feasible #[source]
  return {
    sense
    domainType := domain
    valueType := type.getAppArgs[1]!
    binders := #[{ name := `x, type := domain }]
    objective := ← mkAppM ``Problem.objective #[source]
    constraints := if noConstraints then #[] else #[{ name := `bounds, predicate := feasible }]
  }

def requireForm (presentation : Elab.Reformulation.PresentationState)
    (certifiedRows : Array (Option (Array Elab.Conic.RowResult)) := #[]) : MetaM Expr := do
  match ← Elab.Conic.buildForm presentation {} certifiedRows with
  | .error error => throwError "expected conic form: {error.reason}"
  | .ok form =>
    if form.hasMVar || form.hasSorry then throwError "incomplete conic form"
    checkWithKernel form
    return form

elab "form_for% " source:term : term => do
  let source ← MorewTest.Affine.elaborate source
  requireForm (← presentationFor source)

elab "max_form_for% " source:term : term => do
  let source ← MorewTest.Affine.elaborate source
  requireForm (← presentationFor source .maximize)

def assertForm (termSyntax : TSyntax `term) (count : Nat)
    (parameterCount : Nat := 0) (noConstraints : Bool := false) : TermElabM Unit := do
  let expression ← MorewTest.Affine.elaborate termSyntax
  lambdaBoundedTelescope expression parameterCount fun parameters source => do
    let presentation ← presentationFor source (noConstraints := noConstraints)
    let form ← requireForm presentation
    let data ← mkProjection form `data
    let rowCount ← whnf (← mkProjection data `rowCount)
    unless ← isDefEq rowCount (mkNatLit count) do
      throwError "expected {count} rows, got {rowCount}"
    let canonical ← presentation.canonicalProblem
    let type ← inferType form
    unless ← isDefEq type.getAppArgs.back! canonical do
      throwError "form represents a different problem"
    for parameter in parameters do
      let type ← whnf (← inferType parameter)
      if type.isAppOf ``Norm || type.isAppOf ``NormedAddCommGroup || type.isAppOf ``NormedSpace ||
          type.isAppOf ``AddCommGroup || type.isAppOf ``_root_.Module then
        if form.containsFVar parameter.fvarId! then
          throwError "conic form captured an unrelated ambient vector-space instance"
    let closed ← mkLambdaFVars parameters form
    if closed.hasFVar || closed.hasMVar then
      throwError "temporary canonical instances escaped the form"
    checkWithKernel closed

def rejectCachedForm (presentation : Elab.Reformulation.PresentationState)
    (certifiedRows : Array (Option (Array Elab.Conic.RowResult)))
    (fragment : String) : MetaM Unit := do
  let .error error ← Elab.Conic.buildForm presentation {} certifiedRows
    | throwError "invalid row cache received a conic form"
  unless (← error.reason.toString).contains fragment do
    throwError "missing cached-row diagnostic: {error.reason}"

def rejectForm (termSyntax : TSyntax `term) (fragment : String) : TermElabM Unit := do
  let source ← MorewTest.Affine.elaborate termSyntax
  let .error error ← Elab.Conic.buildForm (← presentationFor source)
    | throwError "unsupported problem received a conic form"
  unless (← error.reason.toString).contains fragment do
    throwError "missing diagnostic context: {error.reason}"

end MorewTest.Conic.Form
