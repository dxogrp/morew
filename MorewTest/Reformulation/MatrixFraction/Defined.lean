/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-! # Separately compiled matrix-fraction domain certificate for imported continuation -/

namespace MorewTest.Reformulation.MatrixFraction

open Morew Morew.Conic
open scoped Matrix

noncomputable section

def source (n : Nat) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      domain : P.toMatrix.PosDef
      bound : Fn.matrixFrac x P.toMatrix ≤ t

variable (n : Nat)

reformulation domainIntermediate : (source n) := by conic at domain

end
end MorewTest.Reformulation.MatrixFraction
