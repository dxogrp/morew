/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.PrintSupport

/-! Euclidean coordinate shorthand preserves unapplied conic vector projections. -/

namespace MorewTest.Reformulation.EuclideanPrintingConic

open Morew
open MorewTest.Reformulation.PrintDetails (printed)

noncomputable section

def source :=
  problem (x : EuclideanSpace ℝ (Fin 2))
    maximize -‖x‖
    subject to balance : x 0 + x 1 = 1

reformulation target : source := by
  hypograph t
  conic

run_cmd do
  for proofs in #[false, true] do
    let output ← printed ``target proofs
    unless output.contains "x.ofLp)" && output.contains "SOC" &&
        output.contains "x 0 + x 1" do
      Lean.throwError "Euclidean coordinate notation changed a bare vector projection: {output}"

end
end MorewTest.Reformulation.EuclideanPrintingConic
