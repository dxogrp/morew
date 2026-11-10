/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Conic.TerminalCommon

/-! Convert nonlinear rows exactly and normalize affine comparisons to cone membership.
Preserve named affine groups and local definitions. Allocate generated names together and
emit a structural form beside the target. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

-- Store section-dependent expressions with the certificate.
private def validateTerminalConic (form expected : Expr)
    (sense : Morew.ObjectiveSense) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  unless type.isAppOfArity ``Morew.Conic.Form 5 do
    throwError "terminal evidence is not a Conic.Form"
  let represented := type.getAppArgs.back!
  unless ← isDefEq represented expected do
    throwError "terminal conic form does not represent the final canonical problem"
  let data ← mkProjection form `data
  let actualSense ← mkProjection data `sense
  let expectedSense := match sense with
    | .minimize => mkConst ``Morew.ObjectiveSense.minimize
    | .maximize => mkConst ``Morew.ObjectiveSense.maximize
  unless ← isDefEq actualSense expectedSense do
    throwError "terminal conic form has the wrong objective sense"
  pure represented

private def retargetTerminalConic (form target equality : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  let arguments := type.getAppArgs.set! (type.getAppNumArgs - 1) target
  let represents ← mkAppM ``Eq.trans #[← mkProjection form `represents, equality]
  let data ← mkProjection form `data
  pure <| mkAppN (mkConst ``Morew.Conic.Form.mk type.getAppFn.constLevels!)
    (arguments ++ #[data, represents])

private def terminalConicProperty (form : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  pure <| mkAppN (mkConst ``Morew.Conic.Form.isConic type.getAppFn.constLevels!)
    (type.getAppArgs ++ #[form])

private def terminalConicAdapter : TerminalAdapter := {
  description := "conic"
  formSuffix := `conicForm
  propertySuffix := `isConic
  validate := validateTerminalConic
  retarget := retargetTerminalConic
  property := terminalConicProperty
}

/-- Plan an affine conic terminal step and request all generated local names. -/
def prepareTerminalConic (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft :=
  prepareTerminalConeForm Morew.Elab.Conic.Terminal.affineBackend
    terminalConicAdapter `_terminalConic state step

@[morew_reformulation_step Morew.conicStep]
private def elabConic : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| conic) => prepareTerminalConic state step
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
