/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Form
import Morew.Elab.Cone.Terminal

/-! Combine affine objective certification with shared cone constraint planning. -/

namespace Morew.Elab.Conic.Terminal

open Lean Lean.Meta
open Morew.Elab.Reformulation
open Morew.Elab.Cone.Terminal

/-- The affine objective backend used by `conic`. -/
def affineBackend : Backend where
  command := "conic"
  checkObjective presentation provider := do
    match ← reifyObjective presentation provider with
    | .error error =>
      let bound := match presentation.sense with
        | .minimize => "epigraph t"
        | .maximize => "hypograph t"
      return .error { error with
        reason := ← addMessageContext m!"{error.reason}; use `{bound}` before `conic`" }
    | .ok _ => return .ok ()
  buildForm presentation provider rows := Morew.Elab.Conic.buildForm presentation provider rows

/-- Plan exact cone constraint rewrites and certify the final affine objective. -/
def plan (presentation : PresentationState) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Expr.Error Result) :=
  planWith affineBackend presentation provider

end Morew.Elab.Conic.Terminal
