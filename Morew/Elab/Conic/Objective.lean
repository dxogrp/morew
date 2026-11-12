/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Affine
import Morew.Elab.Objective
import Morew.Elab.Expr
import Morew.Elab.State
import Morew.Elab.Evidence

/-! Certify affine real objectives while retaining the declared optimization sense. -/

namespace Morew.Elab.Conic

open Lean Lean.Meta

/-- Check an affine certificate against the current objective and canonical vector spaces. -/
def validateObjectiveCertificate (presentation : Reformulation.PresentationState)
    (certificate : Expr) : MetaM (Except Expr.Error Affine.AffineResult) :=
  State.withIsolatedMVars do
    try
      checkRealObjective presentation
      if (← Expr.hasUnresolved certificate) || (← Evidence.hasPlaceholders certificate) then
        throwError "unresolved metavariables or proof placeholders in affine certificate"
      let expected ← Affine.Space.withCanonicalSpaces #[presentation.domainType] do
        mkAppM ``Morew.Affine.Certified #[presentation.objective]
      unless ← isDefEq (← inferType certificate) expected do
        throwError "affine certificate does not match the current objective and canonical vector spaces"
      checkWithKernel certificate
      let map ← instantiateMVars (← mkProjection certificate `map)
      let pointwiseEquality ← instantiateMVars (← mkProjection certificate `correct)
      for expression in #[map, pointwiseEquality] do
        if (← Expr.hasUnresolved expression) || (← Evidence.hasPlaceholders expression) then
          throwError "affine certificate left unresolved metavariables or proof placeholders"
        checkWithKernel expression
      return .ok { map, pointwiseEquality }
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"objective: {error.toMessageData}" }

/-- Validate assembled affine objective fields before using them in a conic form. -/
def validateObjectiveResult (presentation : Reformulation.PresentationState)
    (objective : Affine.AffineResult) : MetaM (Except Expr.Error Affine.AffineResult) :=
  State.withIsolatedMVars do
    try
      let certificate ← Affine.Space.withCanonicalSpaces #[presentation.domainType] do
        mkAppM ``Morew.Affine.Certified.mk #[objective.map, objective.pointwiseEquality]
      validateObjectiveCertificate presentation certificate
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext m!"objective: {error.toMessageData}" }

/-- Construct an affine map equal to the typed presentation's real objective. -/
def reifyObjective (presentation : Reformulation.PresentationState)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Affine.AffineResult) :=
  State.withIsolatedMVars do
    let fail (expression : Expr) (reason : MessageData) :
        MetaM (Except Expr.Error Affine.AffineResult) := do
      return .error {
        expression
        reason := ← addMessageContext m!"objective: {reason}"
      }
    try
      checkRealObjective presentation
      match ← Affine.reifyAffine presentation.objective provider with
      | .ok result => validateObjectiveResult presentation result
      | .error error => fail error.expression error.reason
    catch error =>
      fail presentation.objective error.toMessageData

end Morew.Elab.Conic
