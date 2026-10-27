/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Rewrite.Registry.Source

namespace MorewTest.Rewrite.Registry.First

/-- Independent imported registration used to check candidate-order invariance. -/
@[morew_nlp]
def first (c : ℝ) :
    Morew.EpigraphRepresentation (MorewTest.Rewrite.Registry.Source.shifted c) :=
  MorewTest.Rewrite.Registry.Source.Scoped.shiftedEpigraph c

-- Ordinary attribute erasure changes this module's active state, not the
-- imported module's exported registrations.
attribute [-morew_nlp] MorewTest.Rewrite.Registry.Source.shiftedGraph

run_elab do
  let entries ← Morew.Elab.Rewrite.Registry.entries .nlp
  if entries.any (·.declaration == ``MorewTest.Rewrite.Registry.Source.shiftedGraph) then
    Lean.throwError "attribute erasure did not deactivate the imported declaration"

end MorewTest.Rewrite.Registry.First
