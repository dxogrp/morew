/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Rewrite.Registry
import Morew.Rewrite.Polyhedral

namespace MorewTest.Rewrite.RegistrySource

/-- A custom head whose implementation is irrelevant to registry lookup. -/
def shifted (c x : ℝ) : ℝ := x + c

@[morew_conic, morew_nlp]
def shiftedGraph (c : ℝ) : Morew.GraphRepresentation (shifted c) where
  Auxiliary := Unit
  target x y _ := y = x + c
  source_iff_exists _ _ := by simp [shifted]

namespace Scoped

def shiftedEpigraph (c : ℝ) : Morew.EpigraphRepresentation (shifted c) where
  Auxiliary := Unit
  target x y _ := x + c ≤ y
  source_iff_exists _ _ := by simp [shifted]

attribute [scoped morew_nlp] shiftedEpigraph

end Scoped

end MorewTest.Rewrite.RegistrySource
