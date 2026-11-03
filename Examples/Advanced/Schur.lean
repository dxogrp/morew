/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Schur-complement reformulation

For a positive-definite matrix `A`, the Schur complement `tI - Bᵀ A⁻¹ B`
is positive semidefinite exactly when the block matrix `[A B; Bᵀ tI]` is
positive semidefinite. We package this equivalence as a custom constraint rule
and use it to obtain a conic problem.
-/

namespace Examples.Advanced.Schur

open Morew Morew.Conic
noncomputable section

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

-- Select the proved equivalence for the Schur constraint, then certify the
-- complete problem. The equivalence proof retains the hypothesis hA.
reformulation schurConic : (schurModel A) := by
  conic at schur using schurCertificate
  conic

#printp schurConic

example : GlobalEquivalence (schurModel A) (schurConic A) := schurConic.equivalence A hA
example : (schurConic.conicForm A).data.toProblem = schurConic A :=
  (schurConic.conicForm A).represents
example : IsConic (schurConic A) := schurConic.isConic A

end
end Examples.Advanced.Schur
