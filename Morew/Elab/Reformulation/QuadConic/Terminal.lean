/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.QuadConic.Terminal
import Morew.Elab.Reformulation.Cone.Terminal

/-! Register `qconic` with the quadratic objective backend and shared cone planner.
Validate and retarget `QuadConic.Form` evidence, checking the stored optimization sense. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def terminalQuadConicAdapter : TerminalAdapter :=
  TerminalAdapter.ofForm ``Morew.QuadConic.Form
    (formDescription := "QuadConic.Form") (description := "quadratic conic")
    (formSuffix := `quadConicForm) (propertySuffix := `isQuadConic)

/-- Plan a quadratic conic terminal step and request all generated local names. -/
def prepareTerminalQuadConic (state : ReformState) (step : Syntax)
    (provided? : Option Term := none) : CommandElabM SurfaceStepDraft := do
  let makeBackend := fun (presentation : PresentationState) => do
    let some provided := provided? | return Morew.Elab.QuadConic.Terminal.backend
    let expected ← Affine.Space.withCanonicalSpaces #[presentation.domainType] do
      let name := match presentation.sense with
        | .minimize => ``Morew.QuadConic.CertifiedMin
        | .maximize => ``Morew.QuadConic.CertifiedMax
      mkAppM name #[presentation.objective]
    let proof ← Cone.elaborateObjectiveCertificate provided expected
    return Morew.Elab.QuadConic.Terminal.backendWithCertificate proof
  Cone.prepareTerminalConeForm makeBackend terminalQuadConicAdapter `_terminalQuadConic state step

@[morew_reformulation_step Morew.quadConicStep]
private def elabQuadConic : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| qconic $[using $provided:term]?) =>
      prepareTerminalQuadConic state step provided
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
