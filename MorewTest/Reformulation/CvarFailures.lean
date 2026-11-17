/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.CommandSupport
import MorewTest.DiagnosticsSupport

/-! # CVaR domain, polarity, and affine-coordinate failures are atomic -/

namespace MorewTest.Reformulation.CvarFailures

open Morew

noncomputable section

elab "assert_cvar_atomic% " nested:command : command =>
  MorewTest.elabNoNewDeclarations nested fun name => m!"failed CVaR rewrite leaked {name}"

def source (n : Nat) (β : ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.cvar β x ≤ t

section MissingParameter

variable (β : ℝ)

#guard_error_fragments ["bound", "real-parameter evidence"] in
assert_cvar_atomic%
reformulation missingParameter : (source 3 β) := by conic at bound

#guard_error_fragments ["bound", "real-parameter evidence"] in
assert_cvar_atomic%
reformulation missingExplicitParameter : (source 3 β) := by
  conic at bound using Rewrite.cvarEpigraph

variable (hβ₀ : 0 ≤ β)

#guard_error_fragments ["bound", "real-parameter evidence"] in
assert_cvar_atomic%
include hβ₀ in
reformulation missingUpper : (source 3 β) := by conic at bound

end MissingParameter

section MissingLower

variable (β : ℝ) (hβ₁ : β < 1)

#guard_error_fragments ["bound", "real-parameter evidence"] in
assert_cvar_atomic%
include hβ₁ in
reformulation missingLower : (source 3 β) := by conic at bound

end MissingLower

#guard_error_fragments ["bound", "real-parameter evidence"] in
assert_cvar_atomic%
reformulation unitParameter : (source 3 1) := by conic at bound

#guard_error_fragments ["bound", "real-parameter evidence"] in
assert_cvar_atomic%
reformulation negativeParameter : (source 3 (-1)) := by conic at bound

variable (n : Nat)

#guard_error_fragments ["bound", "nonempty dimension"] in
assert_cvar_atomic%
reformulation missingDimension : (source n (1 / 2)) := by conic at bound

#guard_error_fragments ["bound", "nonempty dimension"] in
assert_cvar_atomic%
reformulation emptySamples : (source 0 (1 / 2)) := by conic at bound

def reverse :=
  problem (x : Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to bound : t ≤ Fn.cvar (1 / 2) x

def equality :=
  problem (x : Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.cvar (1 / 2) x = t

#guard_error_fragments ["bound", "bound polarity"] in
assert_cvar_atomic%
reformulation reversed : reverse := by conic at bound

#guard_error_fragments ["bound", "bound polarity"] in
assert_cvar_atomic%
reformulation equal : equality := by conic at bound

def nonlinear :=
  problem (x : Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.cvar (1 / 2) (fun i => x i ^ 2) ≤ t

def nonlinearBound :=
  problem (x : Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.cvar (1 / 2) x ≤ t ^ 2

#guard_error_fragments ["bound", "power"] in
assert_cvar_atomic%
reformulation nonlinearLosses : nonlinear := by conic at bound

private theorem three_pos : 0 < 3 := by decide
private theorem half_domain : 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 := by norm_num

#guard_error_fragments ["bound", "power"] in
assert_cvar_atomic%
reformulation nonlinearLimit : nonlinearBound := by
  conic at bound using (Rewrite.cvarEpigraph (1 / 2) three_pos half_domain)

def variableParameter :=
  problem (β : ℝ) (x : Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to
      lower : 0 ≤ β
      upper : β < 1
      bound : Fn.cvar β x ≤ t

#guard_error_fragments ["bound", "missing domain evidence"] in
assert_cvar_atomic%
reformulation variableTarget : variableParameter := by conic at bound

def familyParameter (β : ℝ → ℝ) :=
  problem (z : ℝ) (x : Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.cvar (β z) x ≤ t

section UniversalParameter

variable (β : ℝ → ℝ) (hβ : ∀ z, 0 ≤ β z ∧ β z < 1)

#guard_error_fragments ["bound", "missing domain evidence"] in
assert_cvar_atomic%
include hβ in
reformulation familyTarget : (familyParameter β) := by conic at bound

end UniversalParameter

def chained (β : ℝ) :=
  problem (x : Fin 3 → ℝ) (t : ℝ)
    minimize t
    subject to
      first : x 0 ^ 2 ≤ t
      bound : Fn.cvar β x ≤ t

variable (β : ℝ)

#guard_error_fragments ["bound", "real-parameter evidence"] in
assert_cvar_atomic%
reformulation failedChain : (chained β) certificate chainAlias := by
  conic at first
  conic at bound

def objective (β : ℝ) :=
  problem (x : Fin 3 → ℝ) minimize Fn.cvar β x

#guard_error_fragments ["epigraph_t", "real-parameter evidence"] in
assert_cvar_atomic%
reformulation failedLift : (objective β) := by
  epigraph t
  conic

run_cmd do
  let env ← Lean.getEnv
  for name in #[`missingParameter, `missingExplicitParameter, `missingUpper, `missingLower,
      `unitParameter, `negativeParameter, `missingDimension, `emptySamples,
      `reversed, `equal, `nonlinearLosses, `nonlinearLimit, `variableTarget,
      `familyTarget, `failedChain, `chainAlias, `failedLift] do
    let full := `MorewTest.Reformulation.CvarFailures ++ name
    if env.contains full || (Syntax.getProblemView? env full).isSome ||
        (Syntax.getProblemDisplayView? env full).isSome ||
        (Syntax.getProblemPrintPresentation? env full).isSome then
      Lean.throwError "failed CVaR rewrite retained {full}"

end
end MorewTest.Reformulation.CvarFailures
