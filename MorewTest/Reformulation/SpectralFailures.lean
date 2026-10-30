/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Spectral atom boundaries and typed norm selection

Failures must retain the selected label and roll back generated declarations.
Explicit spectral-norm selection must not reinterpret another matrix norm.
-/

namespace MorewTest.Reformulation.SpectralFailures

open Morew Morew.Conic

noncomputable section

elab "assert_spectral_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  if let some name := MorewTest.newLocalDeclaration? before (← Lean.getEnv) then
    Lean.throwError m!"failed spectral rewrite leaked declaration {name}"

section OperatorNorm

open scoped Matrix.Norms.L2Operator

def normSource :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖A‖ ≤ t

def reverseNorm :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : t ≤ ‖A‖

#guard_error_fragments ["bound", "bound polarity"] in
assert_spectral_atomic%
reformulation rejectedReverseNorm : reverseNorm := by conic at bound

def equalityNorm :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖A‖ = t

#guard_error_fragments ["bound", "bound polarity"] in
assert_spectral_atomic%
reformulation rejectedEqualityNorm : equalityNorm := by conic at bound

def bilinearNorm :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖A.transpose * A‖ ≤ t

#guard_error_fragments ["bound", "both matrix factors"] in
assert_spectral_atomic%
reformulation rejectedBilinearNorm : bilinearNorm := by conic at bound

def nonlinearNormBound :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖A‖ ≤ t ^ 2

#guard_error_fragments ["bound", "power"] in
assert_spectral_atomic%
reformulation rejectedNonlinearNormBound : nonlinearNormBound := by conic at bound

def complexNorm :=
  problem (A : Matrix (Fin 2) (Fin 3) ℂ) (t : ℝ)
    minimize t
    subject to bound : ‖A‖ ≤ t

#guard_error_fragments ["bound", "conic rule"] in
assert_spectral_atomic%
reformulation rejectedComplexNorm : complexNorm := by conic at bound

#guard_error_fragments ["bound", "unsupported type or instance", "ℂ"] in
assert_spectral_atomic%
reformulation rejectedExplicitComplexNorm : complexNorm := by
  conic at bound using Conic.Spectral.spectralNormEpigraph

#guard_error_fragments ["unknown or stale constraint label `absent`"] in
assert_spectral_atomic%
reformulation rejectedUnknownLabel : normSource := by conic at absent

#guard_error_fragments ["unknown or stale constraint label `bound`"] in
assert_spectral_atomic%
reformulation rejectedStaleLabel : normSource := by
  conic at bound
  conic at bound

/-- A downstream alias retains its own identity during rule selection. -/
def customSpectralNormEpigraph {m n : Nat} :
    EpigraphRepresentation (fun A : Matrix (Fin m) (Fin n) ℝ => ‖A‖) :=
  Conic.Spectral.spectralNormEpigraph

section Ambiguity

attribute [local morew_conic] customSpectralNormEpigraph

#guard_error_fragments ["bound", "ambiguous exact conic rules", "spectralNormEpigraph",
  "customSpectralNormEpigraph"] in
assert_spectral_atomic%
reformulation rejectedAmbiguousTargeted : normSource := by conic at bound

#guard_error_fragments ["bound", "ambiguous exact conic rules", "spectralNormEpigraph",
  "customSpectralNormEpigraph"] in
assert_spectral_atomic%
reformulation rejectedAmbiguousTerminal : normSource := by conic

reformulation selectedBuiltIn : normSource := by
  conic at bound using Conic.Spectral.spectralNormEpigraph
  conic

reformulation selectedAlias : normSource := by
  conic at bound using customSpectralNormEpigraph
  conic

example : GlobalEquivalence normSource selectedBuiltIn := selectedBuiltIn.equivalence
example : GlobalEquivalence normSource selectedAlias := selectedAlias.equivalence
example : selectedAlias.conicForm.data.rowCount = 2 := rfl

end Ambiguity

reformulation recoveredNorm : normSource := by conic
example : recoveredNorm.conicForm.data.rowCount = 2 := rfl

end OperatorNorm

section ElementwiseNorm

open scoped Matrix.Norms.Elementwise

def entrywiseNorm :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖A‖ ≤ t

#guard_error_fragments ["bound", "unsupported type or instance", "Matrix.normedAddCommGroup"] in
assert_spectral_atomic%
reformulation rejectedEntrywiseAsSpectral : entrywiseNorm := by
  conic at bound using Conic.Spectral.spectralNormEpigraph

end ElementwiseNorm

section FrobeniusNorm

open scoped Matrix.Norms.Frobenius

def frobeniusNorm :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖A‖ ≤ t

#guard_error_fragments ["bound", "unsupported type or instance", "Matrix.frobeniusNormedAddCommGroup"] in
assert_spectral_atomic%
reformulation rejectedFrobeniusAsSpectral : frobeniusNorm := by
  conic at bound using Conic.Spectral.spectralNormEpigraph

end FrobeniusNorm

def reverseNuclear :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : t ≤ Fn.nuclearNorm A

#guard_error_fragments ["bound", "bound polarity"] in
assert_spectral_atomic%
reformulation rejectedReverseNuclear : reverseNuclear := by conic at bound

def equalityNuclear :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.nuclearNorm A = t

#guard_error_fragments ["bound", "bound polarity"] in
assert_spectral_atomic%
reformulation rejectedEqualityNuclear : equalityNuclear := by conic at bound

def nonlinearNuclear :=
  problem (x t : ℝ)
    minimize t
    subject to bound : Fn.nuclearNorm !![x ^ 2, 0] ≤ t

#guard_error_fragments ["bound", "power"] in
assert_spectral_atomic%
reformulation rejectedNonlinearNuclear : nonlinearNuclear := by conic at bound

#guard_error_fragments ["type mismatch", "ℂ", "ℝ"] in
example (A : Matrix (Fin 2) (Fin 3) ℂ) : ℝ := Fn.nuclearNorm A

def reverseLargest :=
  problem (A : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to bound : t ≤ Fn.lambdaMax A.toMatrix

#guard_error_fragments ["bound", "bound polarity"] in
assert_spectral_atomic%
reformulation rejectedReverseLargest : reverseLargest := by conic at bound

def equalityLargest :=
  problem (A : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to bound : Fn.lambdaMax A.toMatrix = t

#guard_error_fragments ["bound", "bound polarity"] in
assert_spectral_atomic%
reformulation rejectedEqualityLargest : equalityLargest := by conic at bound

def missingSymmetry :=
  problem (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.lambdaMax A ≤ t

#guard_error_fragments ["bound", "global matrix symmetry"] in
assert_spectral_atomic%
reformulation rejectedMissingSymmetry : missingSymmetry := by conic at bound

def nonlinearLargest :=
  problem (x t : ℝ)
    minimize t
    subject to bound : Fn.lambdaMax (Matrix.diagonal ![x ^ 2, 1]) ≤ t

#guard_error_fragments ["bound", "power"] in
assert_spectral_atomic%
reformulation rejectedNonlinearLargest : nonlinearLargest := by conic at bound

def emptyLargest :=
  problem (A : SymmetricMatrix 0) (t : ℝ)
    minimize t
    subject to bound : Fn.lambdaMax A.toMatrix ≤ t

#guard_error_fragments ["bound", "nonempty dimension"] in
assert_spectral_atomic%
reformulation rejectedEmptyLargest : emptyLargest := by conic at bound

def symbolicLargest (n : Nat) :=
  problem (A : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to bound : Fn.lambdaMax A.toMatrix ≤ t

variable (n : Nat)

#guard_error_fragments ["bound", "nonempty dimension"] in
assert_spectral_atomic%
reformulation rejectedMissingDimension : (symbolicLargest n) := by conic at bound

#guard_error_fragments ["type mismatch", "ℂ", "ℝ"] in
example (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Fn.lambdaMax A

assert_not_exists rejectedReverseNorm rejectedEqualityNorm rejectedBilinearNorm
  rejectedNonlinearNormBound rejectedComplexNorm rejectedExplicitComplexNorm
  rejectedUnknownLabel rejectedStaleLabel rejectedAmbiguousTargeted rejectedAmbiguousTerminal
  rejectedEntrywiseAsSpectral rejectedFrobeniusAsSpectral rejectedReverseNuclear
  rejectedEqualityNuclear rejectedNonlinearNuclear rejectedReverseLargest rejectedEqualityLargest
  rejectedMissingSymmetry rejectedNonlinearLargest rejectedEmptyLargest rejectedMissingDimension

end

end MorewTest.Reformulation.SpectralFailures
