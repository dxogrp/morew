/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Rewrite.RegistrySource

namespace MorewTest.Rewrite.RegistryFirst

/-- Independent imported registration used to check candidate-order invariance. -/
@[morew_nlp]
def first (c : ℝ) :
    Morew.EpigraphRepresentation (MorewTest.Rewrite.RegistrySource.shifted c) :=
  MorewTest.Rewrite.RegistrySource.Scoped.shiftedEpigraph c

-- Ordinary attribute erasure changes this module's active state, not the
-- imported module's exported registrations.
attribute [-morew_nlp] MorewTest.Rewrite.RegistrySource.shiftedGraph

run_elab do
  let entries ← Morew.Elab.Rewrite.Registry.entries .nlp
  if entries.any (·.declaration == ``MorewTest.Rewrite.RegistrySource.shiftedGraph) then
    Lean.throwError "attribute erasure did not deactivate the imported declaration"

end MorewTest.Rewrite.RegistryFirst
