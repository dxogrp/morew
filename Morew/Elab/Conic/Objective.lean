/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Affine
import Morew.Elab.Reformulation.Presentation
import Morew.Elab.Expr
import Morew.Elab.State

/-! Certify affine real objectives while retaining the declared optimization sense. -/

namespace Morew.Elab.Conic

open Lean Lean.Meta

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
      if (← Expr.hasUnresolved presentation.valueType) ||
          (← Expr.hasUnresolved presentation.domainType) ||
          (← Expr.hasUnresolved presentation.objective) then
        return ← fail presentation.objective "unresolved metavariables in typed objective"
      unless (← whnf presentation.valueType).isConstOf ``Real do
        return ← fail presentation.objective "expected a real-valued objective"
      let expected ← mkArrow presentation.domainType presentation.valueType
      unless ← isDefEq (← inferType presentation.objective) expected do
        return ← fail presentation.objective
          "objective function does not match its presentation domain and value type"
      match ← Affine.reifyAffine presentation.objective provider with
      | .ok result => return .ok result
      | .error error => fail error.expression error.reason
    catch error =>
      fail presentation.objective error.toMessageData

end Morew.Elab.Conic
