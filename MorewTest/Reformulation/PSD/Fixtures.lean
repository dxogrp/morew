/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax
import Morew.Conic.PSD
import Morew.Rewrite.Basic

/-! # Shared PSD sources and Schur certificate for success and failure tests -/

namespace MorewTest.Reformulation.PositiveSemidefinite

open Morew Morew.Conic

noncomputable section

def diagonalSource :=
  problem (x : ℝ)
    let matrix := Matrix.diagonal ![x, 1]
    minimize x
    subject to
      semidefinite : matrix.PosSemidef
      upper : x ≤ 3

/-- A reusable exact certificate, with no global automatic registration. -/
def schurRule (A : SymmetricMatrix 1) (hA : A.toMatrix.PosDef) :
    ExactConstraintLift (fun p : Matrix (Fin 1) (Fin 1) ℝ × ℝ =>
      (Matrix.diagonal ![p.2] - p.1.transpose * A.toMatrix⁻¹ * p.1).PosSemidef) :=
  .ofIff (fun p =>
    (fromBlocksFin A.toMatrix p.1 p.1.transpose (Matrix.diagonal ![p.2])).PosSemidef) (by
      intro p
      simpa only [Cone.mem_positiveSemidefinite, SymmetricMatrix.toMatrix_fromBlocks,
        SymmetricMatrix.toMatrix_ofMatrix] using
        schurComplement_mem_iff A p.1
          (SymmetricMatrix.ofMatrix (Matrix.diagonal ![p.2]) (Matrix.isSymm_diagonal _)) hA)

def schurSource (A : SymmetricMatrix 1) :=
  problem (B : Matrix (Fin 1) (Fin 1) ℝ) (t : ℝ)
    minimize t
    subject to
      schur : (Matrix.diagonal ![t] - B.transpose * A.toMatrix⁻¹ * B).PosSemidef
      remaining : |t| ≤ 5

end
end MorewTest.Reformulation.PositiveSemidefinite
