/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.QuadConic.Form
import Morew.Elab.Conic.Terminal

/-! Certify a quadratic objective while using the shared cone-constraint pipeline. -/

namespace Morew.Elab.QuadConic.Terminal

open Lean Lean.Meta

/-- Quadratic objective recognition and final form construction for `qconic`. -/
def backend : Morew.Elab.Conic.Terminal.Backend where
  command := "qconic"
  checkObjective presentation provider := do
    return (← reifyObjective presentation provider).map fun _ => ()
  buildForm presentation provider rows := Morew.Elab.QuadConic.buildForm presentation provider rows

/-- Plan conic constraint rewrites and certify the final quadratic objective. -/
def plan (presentation : Morew.Elab.Reformulation.PresentationState)
    (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Expr.Error Morew.Elab.Conic.Terminal.Result) :=
  Morew.Elab.Conic.Terminal.planWith backend presentation provider

end Morew.Elab.QuadConic.Terminal
