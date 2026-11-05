/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.LogDet.Sources
import MorewTest.Reformulation.PrintSupport

/-! Log-det auxiliaries preserve helper-disabled certification, fresh names, and deterministic printing. -/

namespace MorewTest.Reformulation.LogDet

open Morew Morew.Conic

noncomputable section

set_option morew.affine.maxExpansionDepth 0 in
set_option morew.affine.maxExpansionSteps 0 in
set_option morew.affine.maxExpansionNodes 0 in
reformulation helpersDisabled : (source 2) := by conic

example : GlobalEquiv (source 2) helpersDisabled := helpersDisabled.equiv
example : IsConic helpersDisabled := helpersDisabled.isConic

def collisionSource :=
  problem (X : SymmetricMatrix 2) (bound_aux t : ℝ)
    maximize bound_aux
    subject to
      domain : X.toMatrix.PosDef
      bound : t ≤ Fn.logDet X.toMatrix

reformulation collisionTarget : collisionSource := by conic

run_cmd do
  let compact ← PrintDetails.printed ``collisionTarget false
  let detailed ← PrintDetails.printed ``collisionTarget true
  let again ← PrintDetails.printed ``collisionTarget false
  unless compact == again do
    Lean.throwError "log-det printing is not deterministic"
  for fragment in #["bound_aux_1", "LowerTriangularEntries 2", "Fin 2 → ℝ", "PSD (2 + 2)",
      "EXP", "domain_conic_1", "bound_conic_3"] do
    unless compact.contains fragment && detailed.contains fragment do
      Lean.throwError "log-det presentation lost {fragment}: {compact}"

end
end MorewTest.Reformulation.LogDet
