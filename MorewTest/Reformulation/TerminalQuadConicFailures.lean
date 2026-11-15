/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.DiagnosticsSupport
import MorewTest.CommandSupport

/-! Rejected quadratic terminal commands leave no declarations or presentation metadata. -/

namespace MorewTest.Reformulation.TerminalQuadConicFailures

open Morew
noncomputable section

elab "assert_quadConic_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let target ← match nested with
    | `(command| reformulation $target:ident : $_source:ident
        $[certificate $_alias:ident]? := by $_steps:reformulationStep*) => pure target
    | `(command| reformulation $target:ident : ($_source:term)
        $[certificate $_alias:ident]? := by $_steps:reformulationStep*) => pure target
    | _ => Lean.throwError "expected a reformulation command"
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  MorewTest.elabNoNewDeclarations nested fun name =>
    m!"failed quadratic conversion leaked declaration {name}"
  let after ← Lean.getEnv
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed quadratic conversion leaked presentation metadata"

def source := problem (x : ℝ) minimize x ^ 2 subject to upper : x ≤ 2

namespace FormCollision
def target.quadConicForm : Nat := 17
#guard_error_fragments ["quadConicForm", "already been declared"] in
assert_quadConic_atomic%
reformulation target : source := by qconic
example : target.quadConicForm = 17 := rfl
end FormCollision

namespace PropertyCollision
def target.isQuadConic : Nat := 19
#guard_error_fragments ["isQuadConic", "already been declared"] in
assert_quadConic_atomic%
reformulation target : source := by qconic
example : target.isQuadConic = 19 := rfl
end PropertyCollision

#guard_error_fragments ["duplicate generated declaration name"] in
assert_quadConic_atomic%
reformulation aliasIsForm : source certificate aliasIsForm.quadConicForm := by qconic

#guard_error_fragments ["duplicate generated declaration name"] in
assert_quadConic_atomic%
reformulation aliasIsProperty : source certificate aliasIsProperty.isQuadConic := by qconic

/-- error: cannot apply a reformulation step after a terminal step -/
#guard_msgs in
assert_quadConic_atomic%
reformulation afterTerminal : source := by
  qconic
  epigraph t

def unsupported := problem (x : ℝ) minimize Real.exp x
#guard_error_fragments ["uncertified"] in
assert_quadConic_atomic%
reformulation unsupportedTarget : unsupported := by qconic

def wrongCurvature := problem (x : ℝ) minimize -(x ^ 2)
#guard_error_fragments ["curvature"] in
assert_quadConic_atomic%
reformulation wrongCurvatureTarget : wrongCurvature := by qconic

-- Curvature is global, even if this feasible set makes the objective constant.
def feasibleOnly := problem (x : ℝ) minimize -(x ^ 2) subject to fixed : x = 0
#guard_error_fragments ["curvature"] in
assert_quadConic_atomic%
reformulation feasibleOnlyTarget : feasibleOnly := by qconic

def unsupportedRow := problem (x : ℝ) minimize x ^ 2 subject to cubic : x ^ 3 = 1
#guard_error_fragments ["cubic"] in
assert_quadConic_atomic%
reformulation unsupportedRowTarget : unsupportedRow := by qconic

-- Reusing a failed name must succeed, including all generated companions.
reformulation wrongCurvatureTarget : source := by qconic
example : IsQuadConic wrongCurvatureTarget := wrongCurvatureTarget.isQuadConic

section MatrixForms

def matrixSource (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) minimize Fn.quadForm x Q

def matrixMaximum (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) maximize Fn.quadForm x Q

def feasibleMatrix (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ)
    minimize Fn.quadForm x Q
    subject to psd : Q.PosSemidef

def varyingMatrix :=
  problem (Q : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ)
    minimize Fn.quadForm x Q
    subject to psd : Q.PosSemidef

variable (Q P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)

#guard_error_fragments ["curvature"] in
assert_quadConic_atomic%
reformulation missingMatrix : (matrixSource Q) := by qconic

#guard_error_fragments ["curvature"] in
assert_quadConic_atomic%
reformulation feasibleMatrixTarget : (feasibleMatrix Q) := by qconic

#guard_error_fragments ["quadratic"] in
assert_quadConic_atomic%
reformulation varyingMatrixTarget : varyingMatrix := by qconic

variable (hQ : Q.PosSemidef)

#guard_error_fragments ["curvature"] in
assert_quadConic_atomic%
reformulation wrongMatrixDirection : (matrixMaximum Q) := by qconic

-- Reusing the rejected name succeeds once the missing parameter evidence is present.
include hQ in
reformulation missingMatrix : (matrixSource Q) := by qconic

example : IsQuadConic (missingMatrix Q) := missingMatrix.isQuadConic Q hQ

end MatrixForms

end
end MorewTest.Reformulation.TerminalQuadConicFailures
