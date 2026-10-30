/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Native matrix PSD constraints and explicit Schur reformulations

The ordinary matrix entries remain visible. Certification checks affinity and
global symmetry before constructing the symmetric PSD cone coordinates.
-/

namespace Morew.Examples.PositiveSemidefinite

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
example : IsConic diagonalConic := diagonalConic.isConic

-- Package the Schur complement theorem `schurComplement_mem_iff` from
-- `Morew.Conic.PSD` as an exact reformulation rule for PSD constraints.
-- The pivot `A` is assumed positive definite.
def schurCertificate {m n : Nat} (A : SymmetricMatrix m) (hA : A.toMatrix.PosDef) :
    ExactConstraintLift (fun p : Matrix (Fin m) (Fin n) ℝ × ℝ =>
      (Matrix.diagonal (fun _ : Fin n => p.2) - p.1.transpose * A.toMatrix⁻¹ * p.1).PosSemidef) :=
  .ofIff (fun p =>
    SymmetricMatrix.fromBlocks A p.1
      (SymmetricMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin n => p.2))
        (Matrix.isSymm_diagonal _)) ∈ PSD (m + n)) (by
      intro p
      exact schurComplement_mem_iff A p.1
        (SymmetricMatrix.ofMatrix (Matrix.diagonal (fun _ : Fin n => p.2))
          (Matrix.isSymm_diagonal _)) hA)

def schurModel (A : SymmetricMatrix 2) :=
  problem (B : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    minimize t
    subject to
      schur : (Matrix.diagonal (fun _ : Fin 2 => t) - B.transpose * A.toMatrix⁻¹ * B).PosSemidef

variable (A : SymmetricMatrix 2) (hA : A.toMatrix.PosDef)

reformulation schurConic : (schurModel A) := by
  conic at schur using schurCertificate
  conic

#printp schurConic
example : GlobalEquivalence (schurModel A) (schurConic A) := schurConic.equivalence A hA
example : (schurConic.conicForm A).data.toProblem = schurConic A :=
  (schurConic.conicForm A).represents

end
end Morew.Examples.PositiveSemidefinite
