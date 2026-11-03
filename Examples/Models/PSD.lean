/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Positive semidefinite and positive definite matrix constraints

A native diagonal matrix constraint and a symmetric positive-definite domain
become exact conic programs. Both examples retain their matrix structure and
finish with global equivalence and conic certificates.
-/

namespace Examples.Models.PSD

open Morew Morew.Conic
noncomputable section

def diagonalModel :=
  problem (x : ℝ)
    let matrix := Matrix.diagonal ![x, 1]
    minimize x
    subject to
      semidefinite : matrix.PosSemidef

reformulation diagonalConic : diagonalModel := by conic

#printp diagonalConic
example : GlobalEquivalence diagonalModel diagonalConic := diagonalConic.equivalence
example : IsConic diagonalConic := diagonalConic.isConic

-- Positive definiteness can be reformulated directly as a cone constraint.
def positiveDefiniteModel :=
  problem (P : SymmetricMatrix 2)
    minimize P.toMatrix.trace
    subject to
      domain : P.toMatrix.PosDef
      lower : (P.toMatrix - 1).PosSemidef

reformulation positiveDefiniteConic : positiveDefiniteModel := by conic

#printp positiveDefiniteConic

example : GlobalEquivalence positiveDefiniteModel positiveDefiniteConic :=
  positiveDefiniteConic.equivalence
example : IsConic positiveDefiniteConic := positiveDefiniteConic.isConic

end
end Examples.Models.PSD
