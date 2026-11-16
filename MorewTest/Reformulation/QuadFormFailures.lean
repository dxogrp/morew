/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.CommandSupport
import MorewTest.DiagnosticsSupport

/-! Unsupported matrix-quadratic bounds leave no generated declarations or presentations. -/

namespace MorewTest.Reformulation.QuadFormFailures

open Morew
open scoped Matrix

noncomputable section

elab "assert_quadForm_atomic% " nested:command : command =>
  MorewTest.elabNoNewDeclarations nested fun name =>
    m!"failed matrix-quadratic rewrite leaked declaration {name}"

def source (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      first : x 0 ^ 2 ≤ t
      bound : Fn.quadForm x Q ≤ t

def nativeSource (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : x ⬝ᵥ (Q *ᵥ x) ≤ t

variable (Q P : Matrix (Fin 2) (Fin 2) ℝ) (hP : P.PosSemidef)

#guard_error_fragments ["bound", "missing domain evidence"] in
assert_quadForm_atomic%
reformulation missing : (source Q) certificate missingAlias := by
  conic at first
  conic at bound

#guard_error_fragments ["bound", "missing domain evidence"] in
assert_quadForm_atomic%
reformulation nativeMissing : (nativeSource Q) := by
  conic at bound using Conic.QuadForm.nativeEpigraph

#guard_error_fragments ["bound", "missing domain evidence"] in
assert_quadForm_atomic%
include hP in
reformulation wrongMatrix : (source Q) := by conic

def objective (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) minimize Fn.quadForm x Q

#guard_error_fragments ["epigraph_t", "missing domain evidence"] in
assert_quadForm_atomic%
reformulation failedLift : (objective Q) := by
  epigraph t
  conic

def reverse (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : t ≤ Fn.quadForm x Q

def equality (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : x ⬝ᵥ (Q *ᵥ x) = t

def nonlinear (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.quadForm (fun i => x i ^ 2) Q ≤ t

def nonlinearBound (Q : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : x ⬝ᵥ (Q *ᵥ x) ≤ t ^ 2

variable (hQ : Q.PosSemidef)

#guard_error_fragments ["bound", "bound polarity"] in
assert_quadForm_atomic%
include hQ in
reformulation reversed : (reverse Q) := by conic at bound

#guard_error_fragments ["bound", "bound polarity"] in
assert_quadForm_atomic%
include hQ in
reformulation equal : (equality Q) := by conic at bound

#guard_error_fragments ["bound", "cone coordinates"] in
assert_quadForm_atomic%
include hQ in
reformulation nonlinearTarget : (nonlinear Q) := by conic at bound

#guard_error_fragments ["bound", "cone coordinates"] in
assert_quadForm_atomic%
reformulation nonlinearBoundTarget : (nonlinearBound Q) := by
  conic at bound using (Conic.QuadForm.nativeEpigraph Q hQ)

def variableMatrix :=
  problem (Q : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : Q.PosSemidef
      bound : Fn.quadForm x Q ≤ t

#guard_error_fragments ["bound", "missing domain evidence"] in
assert_quadForm_atomic%
reformulation variableTarget : variableMatrix := by conic at bound

run_cmd do
  let env ← Lean.getEnv
  for name in #[`missing, `missing.equiv, `missingAlias, `nativeMissing, `wrongMatrix,
      `failedLift, `reversed, `equal, `nonlinearTarget, `nonlinearBoundTarget, `variableTarget] do
    let full := `MorewTest.Reformulation.QuadFormFailures ++ name
    if env.contains full || (Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed matrix-quadratic rewrite retained {full}"

-- The failed declaration and certificate names remain available after rollback.
include hQ in
reformulation missing : (source Q) certificate missingAlias := by conic

example : GlobalEquiv (source Q) (missing Q) := missingAlias Q hQ
example : IsConic (missing Q) := missing.isConic Q

end
end MorewTest.Reformulation.QuadFormFailures
