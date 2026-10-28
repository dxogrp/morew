/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Environment

/-!
# Local declaration rollback checks

These helpers compare snapshots from the same module with the same imports.
Imported constants cannot change during the operations under test, so only the
current module's declarations need scanning. Accessing `Environment.constants`
still waits for kernel checking; querying asynchronous declaration information
instead would change that synchronization.

The checks compare names only. Callers must keep their separate assertions about
metavariables, presentation metadata, and other state.
-/

namespace MorewTest

/-- Return a declaration added since `before`, without allocating a list of the
imported environment. Removing a declaration is allowed by this one-way check. -/
def newLocalDeclaration? (before after : Lean.Environment) : Option Lean.Name := Id.run do
  let original := before.constants.map₂
  for (name, _) in after.constants.map₂ do
    unless original.contains name do return some name
  return none

/-- Check both directions so rolling back too far, or exchanging declarations
without changing their count, is also rejected. -/
def sameLocalDeclarationNames (before after : Lean.Environment) : Bool :=
  (newLocalDeclaration? before after).isNone &&
    (newLocalDeclaration? after before).isNone

end MorewTest
