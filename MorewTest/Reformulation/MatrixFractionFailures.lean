/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Matrix-fraction domain and affine-boundary failures

End-to-end failures preserve the original domain, identify the selected row,
and leave no generated declarations behind.
-/

namespace MorewTest.Reformulation.MatrixFractionFailures

open Morew Morew.Conic

noncomputable section

elab "assert_fraction_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  if let some name := MorewTest.newLocalDeclaration? before (← Lean.getEnv) then
    Lean.throwError m!"failed matrix-fraction rewrite leaked declaration {name}"

def missingDomain :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      bound : Fn.matrixFrac x P.toMatrix ≤ t

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_fraction_atomic%
reformulation rejectedMissingTargeted : missingDomain := by conic at bound

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_fraction_atomic%
reformulation rejectedMissingTerminal : missingDomain := by conic

def semidefiniteDomain :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      domain : P.toMatrix.PosSemidef
      bound : Fn.matrixFrac x P.toMatrix ≤ t

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_fraction_atomic%
reformulation rejectedSemidefinite : semidefiniteDomain := by conic

def singularPivot :=
  problem (x : Fin 1 → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : Fn.matrixFrac x (0 : Matrix (Fin 1) (Fin 1) ℝ) ≤ t

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_fraction_atomic%
reformulation rejectedSingular : singularPivot := by conic at bound

def wrongPivot :=
  problem (x : Fin 2 → ℝ) (P Q : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      domain : Q.toMatrix.PosDef
      bound : Fn.matrixFrac x P.toMatrix ≤ t

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_fraction_atomic%
reformulation rejectedWrongPivot : wrongPivot := by conic at bound

def zeroMargin :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      margin : (P.toMatrix - (0 : ℝ) • 1).PosSemidef
      bound : Fn.matrixFrac x P.toMatrix ≤ t

#guard_error_fragments ["bound", "positive-definiteness"] in
assert_fraction_atomic%
reformulation rejectedZeroMargin : zeroMargin := by conic at bound

def nonlinearVector :=
  problem (z : ℝ) (P : SymmetricMatrix 1) (t : ℝ)
    minimize t
    subject to
      domain : P.toMatrix.PosDef
      bound : Fn.matrixFrac ![z ^ 2] P.toMatrix ≤ t

#guard_error_fragments ["bound", "power"] in
assert_fraction_atomic%
reformulation rejectedNonlinearVector : nonlinearVector := by conic at bound

def nonlinearPivot :=
  problem (z : ℝ) (t : ℝ)
    minimize t
    subject to
      domain : (Matrix.diagonal ![z ^ 2 + 1]).PosDef
      bound : Fn.matrixFrac ![1] (Matrix.diagonal ![z ^ 2 + 1]) ≤ t

#guard_error_fragments ["bound", "power"] in
assert_fraction_atomic%
reformulation rejectedNonlinearPivot : nonlinearPivot := by conic at bound

#guard_error_fragments ["domain", "power"] in
assert_fraction_atomic%
reformulation rejectedNonlinearDomain : nonlinearPivot := by conic at domain

def reversed :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      domain : P.toMatrix.PosDef
      bound : t ≤ Fn.matrixFrac x P.toMatrix

#guard_error_fragments ["bound", "bound polarity"] in
assert_fraction_atomic%
reformulation rejectedReverse : reversed := by conic at bound

def equality :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      domain : P.toMatrix.PosDef
      bound : Fn.matrixFrac x P.toMatrix = t

#guard_error_fragments ["bound", "bound polarity"] in
assert_fraction_atomic%
reformulation rejectedEquality : equality := by conic at bound

-- A retained domain justifies the fraction theorem, but generated PSD
-- coordinates still require symmetry at every decision point.
def missingGlobalSymmetry :=
  problem (x : Fin 2 → ℝ) (P : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    minimize t
    subject to
      domain : P.PosDef
      bound : Fn.matrixFrac x P ≤ t

#guard_error_fragments ["bound", "global matrix symmetry"] in
assert_fraction_atomic%
reformulation rejectedMissingSymmetry : missingGlobalSymmetry := by conic at bound

def validSource :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2) (t : ℝ)
    minimize t
    subject to
      domain : P.toMatrix.PosDef
      bound : Fn.matrixFrac x P.toMatrix ≤ t

/-- A downstream alias participates in ordinary exact-rule selection. -/
def customMatrixFracEpigraph {n : Nat} :
    EpigraphRepresentation (fun p : (Fin n → ℝ) ×
      {P : Matrix (Fin n) (Fin n) ℝ // P.PosDef} => Fn.matrixFrac p.1 p.2.1) :=
  Conic.MatrixFraction.epigraph

section Ambiguity

attribute [local morew_conic] customMatrixFracEpigraph

#guard_error_fragments ["bound", "ambiguous exact conic rules", "MatrixFraction.epigraph",
  "customMatrixFracEpigraph"] in
assert_fraction_atomic%
reformulation rejectedAmbiguous : validSource := by conic at bound

reformulation selectedExplicitly : validSource := by
  conic at bound using customMatrixFracEpigraph
  conic

example : GlobalEquivalence validSource selectedExplicitly := selectedExplicitly.equivalence
example : IsConic selectedExplicitly := selectedExplicitly.isConic

end Ambiguity

reformulation recovered : validSource := by conic
example : GlobalEquivalence validSource recovered := recovered.equivalence
example : IsConic recovered := recovered.isConic

assert_not_exists rejectedMissingTargeted rejectedMissingTerminal rejectedSemidefinite
  rejectedSingular rejectedWrongPivot rejectedZeroMargin rejectedNonlinearVector
  rejectedNonlinearPivot rejectedNonlinearDomain rejectedReverse rejectedEquality
  rejectedMissingSymmetry rejectedAmbiguous

end

end MorewTest.Reformulation.MatrixFractionFailures
