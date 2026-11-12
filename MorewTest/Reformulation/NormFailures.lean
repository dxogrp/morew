/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.DiagnosticsSupport
import MorewTest.CommandSupport

/-! # Named norms retain target certification, ambiguity, and transaction boundaries -/

namespace MorewTest.Reformulation.NormFailures

open Morew

noncomputable section

elab "assert_norm_atomic% " nested:command : command =>
  MorewTest.elabNoNewDeclarations nested fun name => m!"failed named-norm rewrite leaked declaration {name}"

def reverse :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : t ≤ Fn.norm2 x

def equal :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.normInf x = t

#guard_error_fragments ["bound", "bound polarity"] in
assert_norm_atomic%
reformulation rejectedReverse : reverse := by conic at bound

#guard_error_fragments ["bound", "bound polarity"] in
assert_norm_atomic%
reformulation rejectedEquality : equal := by conic at bound

#guard_error_fragments ["bound", "no supported exact NLP rule"] in
assert_norm_atomic%
reformulation rejectedReverseNLP : reverse := by nlp at bound

#guard_error_fragments ["bound", "no supported exact NLP rule"] in
assert_norm_atomic%
reformulation rejectedEqualityNLP : equal := by nlp at bound

def nonaffine :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.norm2 (fun i => (x i) ^ 2) ≤ t

#guard_error_fragments ["bound", "power"] in
assert_norm_atomic%
reformulation rejectedNonaffine : nonaffine := by conic at bound

reformulation smoothAccepted : nonaffine := by nlp
example : IsSmoothNLP smoothAccepted := smoothAccepted.isSmoothNLP

def negativeMinimum := problem (x : Fin 2 → ℝ) minimize -Fn.norm1 x

#guard_error_fragments ["epigraph_t", "no supported registered conic rule"] in
assert_norm_atomic%
reformulation rejectedNegativeMinimum : negativeMinimum := by
  epigraph t
  conic

def afterAuxiliary :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      one : Fn.norm1 x ≤ t
      reverse : 1 ≤ Fn.norm2 x

#guard_error_fragments ["reverse", "bound polarity"] in
assert_norm_atomic%
reformulation rejectedAfterAuxiliary : afterAuxiliary certificate failedAlias := by
  conic at one
  conic at reverse

def oneSource :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.norm1 x ≤ t

def customOne {n : Nat} : EpigraphRepr (fun x : Fin n → ℝ => Fn.norm1 x) :=
  Rewrite.fnNorm1Epigraph

section Ambiguous
attribute [local morew_conic, local morew_nlp] customOne

#guard_error_fragments ["bound", "ambiguous exact conic rules", "customOne", "fnNorm1Epigraph"] in
assert_norm_atomic%
reformulation rejectedAmbiguous : oneSource := by conic at bound

#guard_error_fragments ["bound", "ambiguous exact NLP rules", "customOne", "fnNorm1Epigraph"] in
assert_norm_atomic%
reformulation rejectedAmbiguousNLP : oneSource := by nlp

reformulation selectedBuiltIn : oneSource := by
  conic at bound using Rewrite.fnNorm1Epigraph
  conic

reformulation selectedCustom : oneSource := by
  nlp at bound using (customOne (n := 2))
  nlp

example : IsConic selectedBuiltIn := selectedBuiltIn.isConic
example : IsSmoothNLP selectedCustom := selectedCustom.isSmoothNLP
end Ambiguous

reformulation recovered : oneSource := by conic
example : IsConic recovered := recovered.isConic

#guard_error_fragments ["bound", "does not match"] in
assert_norm_atomic%
reformulation wrongNamedRule : oneSource := by
  conic at bound using Rewrite.fnNormInfEpigraph

-- The native rules still check their actual source norm instances. A named
-- helper's registration must never make this altered native norm eligible.
section NativeShadow
local instance : Norm (Fin 2 → ℝ) := ⟨fun _ => 37⟩

def shadowedNative :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖x‖ ≤ t

#guard_error_fragments ["bound", "unsupported type or instance"] in
assert_norm_atomic%
reformulation rejectedShadow : shadowedNative := by
  conic at bound using Rewrite.normInfEpigraph

#guard_error_fragments ["bound", "unsupported type or instance"] in
assert_norm_atomic%
reformulation rejectedShadowNLP : shadowedNative := by
  nlp at bound using Rewrite.normInfEpigraph
end NativeShadow

assert_not_exists rejectedReverse rejectedEquality rejectedReverseNLP rejectedEqualityNLP
  rejectedNonaffine rejectedNegativeMinimum rejectedAfterAuxiliary failedAlias
  rejectedAmbiguous rejectedAmbiguousNLP wrongNamedRule rejectedShadow rejectedShadowNLP

end
end MorewTest.Reformulation.NormFailures
