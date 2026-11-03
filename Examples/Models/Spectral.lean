/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Matrix and spectral reformulations

Largest eigenvalues, Euclidean operator norms, nuclear norms, and matrix
fractions have exact semidefinite representations. The matrix fraction
requires a positive-definite domain. After introducing objective epigraphs,
each script constructs an equivalent conic program.
-/

namespace Examples.Models.Spectral

open Morew Morew.Conic

noncomputable section

-- Minimize the largest eigenvalue of a symmetric matrix with fixed trace.
def largestEigenvalueModel :=
  problem (A : SymmetricMatrix 2)
    minimize Fn.lambdaMax A.toMatrix
    subject to
      normalization : A.toMatrix.trace = 1

reformulation largestEigenvalueConic : largestEigenvalueModel := by
  epigraph t as largest
  conic

#printp largestEigenvalueConic

example : GlobalEquivalence largestEigenvalueModel largestEigenvalueConic :=
  largestEigenvalueConic.equivalence
example : IsConic largestEigenvalueConic := largestEigenvalueConic.isConic

-- The scope selects the Euclidean operator norm in the modeled objective.
open scoped Matrix.Norms.L2Operator in
def operatorNormModel :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize ‖A‖
    subject to
      firstEntry : A 0 0 = 1
      lastEntry : A 1 2 = 2

reformulation operatorNormConic : operatorNormModel := by
  epigraph t as norm_bound
  conic at norm_bound
  conic

#printp operatorNormConic

example : GlobalEquivalence operatorNormModel operatorNormConic :=
  operatorNormConic.equivalence
example : IsConic operatorNormConic := operatorNormConic.isConic

-- A nuclear-norm matrix completion introduces two symmetric matrices and uses
-- exactly half their summed traces as the bound.
def nuclearNormModel :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize Fn.nuclearNorm A
    subject to
      firstEntry : A 0 0 = 1
      secondEntry : A 1 1 = 1

reformulation nuclearNormConic : nuclearNormModel := by
  epigraph t as nuclear_bound
  conic

#printp nuclearNormConic

example : GlobalEquivalence nuclearNormModel nuclearNormConic := nuclearNormConic.equivalence
example : IsConic nuclearNormConic := nuclearNormConic.isConic

-- The Schur representation of the matrix fraction requires positive definiteness.
def matrixFractionModel :=
  problem (x : Fin 2 → ℝ) (P : SymmetricMatrix 2)
    minimize Fn.matrixFrac x P.toMatrix
    subject to
      domain : P.toMatrix.PosDef
      normalization : P.toMatrix.trace = 2
      anchor : x 0 = 1

reformulation matrixFractionConic : matrixFractionModel := by
  epigraph t as fraction_bound
  -- The semidefinite domain representation still proves positive definiteness.
  conic at domain
  conic at fraction_bound
  conic

#printp matrixFractionConic

example : GlobalEquivalence matrixFractionModel matrixFractionConic :=
  matrixFractionConic.equivalence
example : IsConic matrixFractionConic := matrixFractionConic.isConic

end

end Examples.Models.Spectral
