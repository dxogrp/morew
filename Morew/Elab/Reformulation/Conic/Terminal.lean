/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Terminal
import Morew.Elab.Reformulation.Cone.Terminal

/-! Register `conic` with the affine objective backend and shared cone planner.
Validate and retarget `Conic.Form` evidence, checking the stored optimization sense. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

private def terminalConicAdapter : TerminalAdapter :=
  TerminalAdapter.ofForm ``Morew.Conic.Form
    (formDescription := "Conic.Form") (description := "conic")
    (formSuffix := `conicForm) (propertySuffix := `isConic)

/-- Plan an affine conic terminal step and request all generated local names. -/
def prepareTerminalConic (state : ReformState) (step : Syntax)
    (provided? : Option Term := none) : CommandElabM SurfaceStepDraft := do
  let makeBackend := fun (presentation : PresentationState) => do
    let some provided := provided? | return Morew.Elab.Conic.Terminal.backend
    let expected ← Affine.Space.withCanonicalSpaces #[presentation.domainType] do
      mkAppM ``Morew.Affine.Certified #[presentation.objective]
    let proof ← Cone.elaborateObjectiveCertificate provided expected
    return Morew.Elab.Conic.Terminal.backendWithCertificate proof
  Cone.prepareTerminalConeForm makeBackend terminalConicAdapter `_terminalConic state step

@[morew_reformulation_step Morew.conicStep]
private def elabConic : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| conic $[using $provided:term]?) =>
      prepareTerminalConic state step provided
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
