/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.DiagnosticsSupport
import MorewTest.CommandSupport
import MorewTest.ElabSupport

/-! Log-det rewriting preserves domains, instance semantics, and atomic failure. -/

namespace MorewTest.Reformulation.LogDetFailures

open Morew Morew.Conic

noncomputable section

elab "assert_logdet_atomic% " nested:command : command =>
  MorewTest.elabNoNewDeclarations nested fun name => m!"failed log-det rewrite leaked declaration {name}"

def missingDomain :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedMissingTargeted : missingDomain := by conic at bound

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedMissingTerminal : missingDomain := by conic

def nativeMissingDomain :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to bound : t ≤ Real.log X.toMatrix.det

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedNativeMissing : nativeMissingDomain := by
  conic at bound using Morew.Conic.LogDet.nativeHypograph

def semidefiniteDomain :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosSemidef
      bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedSemidefinite : semidefiniteDomain := by conic

def singularMatrix :=
  problem (t : ℝ)
    maximize t
    subject to bound : t ≤ Fn.logDet (0 : Matrix (Fin 1) (Fin 1) ℝ)

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedSingular : singularMatrix := by conic at bound

def positiveDeterminant :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      determinant : 0 < X.toMatrix.det
      bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedPositiveDeterminant : positiveDeterminant := by conic at bound

def indefiniteMatrix :=
  problem (t : ℝ)
    maximize t
    subject to bound : t ≤ Fn.logDet (Matrix.diagonal ![-1, -1])

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedIndefinite : indefiniteMatrix := by conic at bound

def wrongMatrix :=
  problem (X Y : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      domain : Y.toMatrix.PosDef
      bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedWrongMatrix : wrongMatrix := by conic at bound

def zeroMargin :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      margin : (X.toMatrix - (0 : ℝ) • 1).PosSemidef
      bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedZeroMargin : zeroMargin := by conic at bound

def mismatchedWitness :=
  problem (X W : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      witness : SymmetricMatrix.fromBlocks X 0 W ∈ PSD 4
      bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_logdet_atomic%
reformulation rejectedWitness : mismatchedWitness := by conic at bound

def nonlinearMatrix :=
  problem (z t : ℝ)
    maximize t
    subject to
      domain : (Matrix.diagonal ![z ^ 2 + 1]).PosDef
      bound : t ≤ Fn.logDet (Matrix.diagonal ![z ^ 2 + 1])

#guard_error_fragments ["bound", "power"] in
assert_logdet_atomic%
reformulation rejectedNonlinearMatrix : nonlinearMatrix := by conic at bound

def nonlinearBound :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : t ^ 2 ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "power"] in
assert_logdet_atomic%
reformulation rejectedNonlinearBound : nonlinearBound := by conic at bound

def reverse :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : Fn.logDet X.toMatrix ≤ t

#guard_error_fragments ["bound", "bound polarity"] in
assert_logdet_atomic%
reformulation rejectedReverse : reverse := by conic at bound

def equality :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : Fn.logDet X.toMatrix = t

#guard_error_fragments ["bound", "bound polarity"] in
assert_logdet_atomic%
reformulation rejectedEquality : equality := by conic at bound

def missingGlobalSymmetry :=
  problem (X : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    maximize t
    subject to
      domain : X.PosDef
      bound : t ≤ Fn.logDet X

#guard_error_fragments ["bound", "global matrix symmetry"] in
assert_logdet_atomic%
reformulation rejectedSymmetry : missingGlobalSymmetry := by conic at bound

def emptyDimension :=
  problem (X : SymmetricMatrix 0) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["bound", "nonempty dimension"] in
assert_logdet_atomic%
reformulation rejectedEmpty : emptyDimension := by
  conic at bound using Morew.Conic.LogDet.hypograph

#guard_error_fragments ["bound", "nonempty dimension"] in
assert_logdet_atomic%
reformulation rejectedEmptyAutomatic : emptyDimension := by conic at bound

#guard_error_fragments ["bound", "nonempty dimension"] in
assert_logdet_atomic%
reformulation rejectedEmptyTerminal : emptyDimension := by conic

def alteredOrder :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : @LE.le ℝ ⟨fun _ _ => t ≤ Fn.logDet X.toMatrix⟩ t (Fn.logDet X.toMatrix)

#guard_error_fragments ["bound"] in
assert_logdet_atomic%
reformulation rejectedOrder : alteredOrder := by
  conic at bound using Morew.Conic.LogDet.hypograph

def alteredNegation :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      domain : X.toMatrix.PosDef
      bound : @Neg.neg ℝ ⟨fun _ => -Fn.logDet X.toMatrix⟩ (Fn.logDet X.toMatrix) ≤ t

#guard_error_fragments ["bound"] in
assert_logdet_atomic%
reformulation rejectedNegation : alteredNegation := by
  conic at bound using Morew.Conic.LogDet.hypograph

def validSource :=
  problem (X : SymmetricMatrix 2) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : t ≤ Fn.logDet X.toMatrix

#guard_error_fragments ["unknown or stale constraint label `bound`"] in
assert_logdet_atomic%
reformulation rejectedStaleLabel : validSource := by
  conic at bound
  conic at bound

/-- A downstream alias remains a distinct candidate. -/
def customLogDetHypograph {n : Nat} (hn : 0 < n) :
    HypographRepr
      (fun X : {X : Matrix (Fin n) (Fin n) ℝ // X.PosDef} => Fn.logDet X.1) :=
  Morew.Conic.LogDet.hypograph hn

section Ambiguity

attribute [local morew_conic] customLogDetHypograph

#guard_error_fragments ["bound", "ambiguous exact conic rules", "LogDet.hypograph",
  "customLogDetHypograph"] in
assert_logdet_atomic%
reformulation rejectedAmbiguous : validSource := by conic at bound

reformulation selectedExplicitly : validSource := by
  conic at bound using customLogDetHypograph
  conic

example : GlobalEquiv validSource selectedExplicitly := selectedExplicitly.equiv
example : IsConic selectedExplicitly := selectedExplicitly.isConic

end Ambiguity

section NativeScalarAmbiguity

def fixedNativeSource (X : Matrix (Fin 2) (Fin 2) ℝ) :=
  problem (t : ℝ)
    maximize t
    subject to bound : t ≤ Real.log X.det

variable (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X.PosDef) (hdet : 0 < X.det)

#guard_error_fragments ["bound", "ambiguous exact conic rules", "Exponential.logHypograph",
  "LogDet.nativeHypograph"] in
assert_logdet_atomic%
reformulation rejectedNativeScalarAmbiguity : (fixedNativeSource X) := by conic at bound

reformulation selectedNative : (fixedNativeSource X) := by
  conic at bound using Morew.Conic.LogDet.nativeHypograph
  conic

example : GlobalEquiv (fixedNativeSource X) (selectedNative X hX) :=
  selectedNative.equiv X hX
example : IsConic (selectedNative X hX) := selectedNative.isConic X hX

reformulation selectedScalar : (fixedNativeSource X) := by
  conic at bound using Exponential.logHypograph
  conic

example : GlobalEquiv (fixedNativeSource X) (selectedScalar X) :=
  selectedScalar.equiv X hdet
example : IsConic (selectedScalar X) := selectedScalar.isConic X

end NativeScalarAmbiguity

reformulation recovered : validSource := by conic
example : GlobalEquiv validSource recovered := recovered.equiv
example : IsConic recovered := recovered.isConic

-- The contextual theorem still applies when its retained domain is infeasible.
-- It must not silently replace that domain with positive determinant alone.
def infeasibleSingular :=
  problem (t : ℝ)
    maximize t
    subject to
      domain : (0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef
      bound : t ≤ Fn.logDet (0 : Matrix (Fin 1) (Fin 1) ℝ)

reformulation infeasibleSingularTarget : infeasibleSingular := by
  conic at bound
  conic
example : GlobalEquiv infeasibleSingular infeasibleSingularTarget :=
  infeasibleSingularTarget.equiv

def infeasibleIndefinite :=
  problem (t : ℝ)
    maximize t
    subject to
      domain : (Matrix.diagonal ![-1, -1] : Matrix (Fin 2) (Fin 2) ℝ).PosDef
      bound : t ≤ Fn.logDet (Matrix.diagonal ![-1, -1])

reformulation infeasibleIndefiniteTarget : infeasibleIndefinite := by
  conic at bound
  conic
example : GlobalEquiv infeasibleIndefinite infeasibleIndefiniteTarget :=
  infeasibleIndefiniteTarget.equiv

assert_not_exists rejectedMissingTargeted rejectedMissingTerminal rejectedNativeMissing
  rejectedSemidefinite
  rejectedSingular rejectedPositiveDeterminant rejectedIndefinite rejectedWrongMatrix
  rejectedZeroMargin rejectedWitness rejectedNonlinearMatrix rejectedNonlinearBound
  rejectedReverse rejectedEquality rejectedSymmetry rejectedEmpty rejectedEmptyAutomatic
  rejectedEmptyTerminal rejectedOrder rejectedNegation rejectedStaleLabel
  rejectedAmbiguous rejectedNativeScalarAmbiguity

open Lean Lean.Meta Lean.Elab.Term Lean.Elab.Command in
run_cmd liftTermElabM do
  let source ← elaborateUnchecked (← `(fun p : SymmetricMatrix 2 × ℝ =>
    p.2 ≤ Fn.logDet p.1.toMatrix))
  let sentinel ← mkFreshExprMVar (mkConst ``Real)
  let before ← getMCtx
  let environment ← getEnv
  let .error _ ← Morew.Elab.Cone.Rewrite.planUnique source
    | throwError "log-det planning accepted a matrix without a domain"
  assertMVarAllocationStateUnchanged before "failed log-det planning leaked scratch metavariables"
  if ← sentinel.mvarId!.isAssigned then
    throwError "failed log-det planning assigned a caller metavariable"
  if let some name := MorewTest.newLocalDeclaration? environment (← getEnv) then
    throwError "failed log-det planning leaked declaration {name}"

end
end MorewTest.Reformulation.LogDetFailures
