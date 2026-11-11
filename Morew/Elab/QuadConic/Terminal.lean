/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.QuadConic.Form
import Morew.Elab.Cone.Terminal

/-! Combine quadratic objective certification with shared cone constraint planning. -/

namespace Morew.Elab.QuadConic.Terminal

open Lean Lean.Meta

/-- Quadratic objective recognition and final form construction for `qconic`. -/
def backend : Morew.Elab.Cone.Terminal.Backend where
  command := "qconic"
  checkObjective presentation provider := do
    return (← reifyObjective presentation provider).map fun _ => ()
  buildForm presentation _ provider rows := Morew.Elab.QuadConic.buildForm presentation provider rows

/-- Use a supplied quadratic objective throughout normalization and constraint planning. -/
def backendWithCertificate (certificate : Expr) : Morew.Elab.Cone.Terminal.Backend where
  command := "qconic"
  checkObjective presentation _ := do
    return (← validateObjectiveCertificate presentation certificate).map fun _ => ()
  buildForm presentation projection provider rows := do
    let transported ← Affine.Space.withCanonicalSpaces #[presentation.domainType] do
      let comp := match presentation.sense with
        | .minimize => ``Morew.QuadConic.CertifiedMin.comp
        | .maximize => ``Morew.QuadConic.CertifiedMax.comp
      mkAppM comp #[certificate, projection]
    match ← validateObjectiveCertificate presentation transported with
    | .error error => return .error error
    | .ok objective => buildFormWithObjective presentation objective provider rows

/-- Plan conic constraint rewrites and certify the final quadratic objective. -/
def plan (presentation : Morew.Elab.Reformulation.PresentationState)
    (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Expr.Error Morew.Elab.Cone.Terminal.Result) :=
  Morew.Elab.Cone.Terminal.planWith backend presentation provider

end Morew.Elab.QuadConic.Terminal
