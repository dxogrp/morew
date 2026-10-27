/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-! # Imported registered rules used by command integration tests -/

namespace MorewTest.Reformulation.RegistrySource

open Morew

noncomputable section

/-- A named helper stays opaque to automatic expression certification. -/
def shiftedAbs (center x : ℝ) : ℝ := |x - center|

/-- One parameterized exact record can support both target languages. -/
@[morew_conic, morew_nlp]
def shiftedAbsEpigraph (center : ℝ) : EpigraphRepresentation (shiftedAbs center) where
  Auxiliary := Unit
  target x t _ := x - center ≤ t ∧ -(x - center) ≤ t
  source_iff_exists x t := Rewrite.absEpigraph.source_iff_exists (x - center) t

def source (center : ℝ) :=
  problem (x t : ℝ)
    let loss := shiftedAbs center x
    minimize t
    subject to
      before : 0 ≤ x
      bound : loss ≤ t
      after : t ≤ 10

def maximizing (center : ℝ) :=
  problem (x t : ℝ)
    maximize -t
    subject to
      bound : shiftedAbs center x ≤ t

end

end MorewTest.Reformulation.RegistrySource
