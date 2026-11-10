/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.QuadConic.Terminal
import Morew.Elab.Reformulation.Conic.TerminalCommon

/-! Convert nonlinear rows exactly and normalize affine comparisons to cone membership.
Preserve named affine groups and local definitions. Allocate generated names together and
emit a quadratic structural form beside the target. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

-- Store section-dependent expressions with the certificate.
private def validateTerminalQuadConic (form expected : Expr)
    (sense : Morew.ObjectiveSense) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  unless type.isAppOfArity ``Morew.QuadConic.Form 5 do
    throwError "terminal evidence is not a QuadConic.Form"
  let represented := type.getAppArgs.back!
  unless ← isDefEq represented expected do
    throwError "terminal quadratic conic form does not represent the final canonical problem"
  let data ← mkProjection form `data
  let actualSense ← mkProjection data `sense
  let expectedSense := match sense with
    | .minimize => mkConst ``Morew.ObjectiveSense.minimize
    | .maximize => mkConst ``Morew.ObjectiveSense.maximize
  unless ← isDefEq actualSense expectedSense do
    throwError "terminal quadratic conic form has the wrong objective sense"
  pure represented

private def retargetTerminalQuadConic (form target equality : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  let arguments := type.getAppArgs.set! (type.getAppNumArgs - 1) target
  let represents ← mkAppM ``Eq.trans #[← mkProjection form `represents, equality]
  let data ← mkProjection form `data
  pure <| mkAppN (mkConst ``Morew.QuadConic.Form.mk type.getAppFn.constLevels!)
    (arguments ++ #[data, represents])

private def terminalQuadConicProperty (form : Expr) : TermElabM Expr := do
  let type ← whnf (← inferType form)
  pure <| mkAppN (mkConst ``Morew.QuadConic.Form.isQuadConic type.getAppFn.constLevels!)
    (type.getAppArgs ++ #[form])

private def terminalQuadConicAdapter : TerminalAdapter := {
  description := "quadratic conic"
  formSuffix := `quadConicForm
  propertySuffix := `isQuadConic
  validate := validateTerminalQuadConic
  retarget := retargetTerminalQuadConic
  property := terminalQuadConicProperty
}

/-- Plan a quadratic conic terminal step and request all generated local names. -/
def prepareTerminalQuadConic (state : ReformState) (step : Syntax) :
    CommandElabM SurfaceStepDraft :=
  prepareTerminalConeForm Morew.Elab.QuadConic.Terminal.backend
    terminalQuadConicAdapter `_terminalQuadConic state step

@[morew_reformulation_step Morew.quadConicStep]
private def elabQuadConic : StepHandler := fun state step => do
  match step with
  | `(reformulationStep| qconic) => prepareTerminalQuadConic state step
  | _ => throwUnsupportedSyntax

end Morew.Elab.Reformulation
