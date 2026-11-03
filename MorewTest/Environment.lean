/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Environment

/-!
# Local declaration rollback checks

Compare declaration names within one module and fixed imports.
`Environment.constants` waits for kernel checking. Metavariables, presentation
metadata, and other state require separate assertions.
-/

namespace MorewTest

/-- Return a declaration added since `before`, without allocating a list of the
imported environment. Removing a declaration is allowed by this one-way check. -/
def newLocalDeclaration? (before after : Lean.Environment) : Option Lean.Name := Id.run do
  let original := before.constants.map₂
  for (name, _) in after.constants.map₂ do
    unless original.contains name do return some name
  return none

/-- Check both directions to detect removals and replacements as well as additions. -/
def sameLocalDeclarationNames (before after : Lean.Environment) : Bool :=
  (newLocalDeclaration? before after).isNone &&
    (newLocalDeclaration? after before).isNone

end MorewTest
