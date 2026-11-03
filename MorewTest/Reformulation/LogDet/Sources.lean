/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax
import Morew.Conic.PSD
import Morew.Fn.Matrix

/-! Shared named and native log-determinant source problems. -/

namespace MorewTest.Reformulation.LogDet

open Morew Morew.Conic

noncomputable section

def source (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      domain : X.toMatrix.PosDef
      bound : t ≤ Fn.logDet X.toMatrix

def reverseSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    minimize -t
    subject to
      bound : Real.log X.toMatrix.det ≥ t
      domain : X.toMatrix.PosDef

end
end MorewTest.Reformulation.LogDet
