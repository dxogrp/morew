/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.State

/-!
# Compatibility API for affine state isolation

State isolation is shared by proof-producing elaborators in `Morew.Elab.State`.
This module retains the affine entry point for existing callers.
-/

namespace Morew.Elab.Affine

open Lean Lean.Meta

/-- Compatibility wrapper for shared metavariable and environment isolation. -/
abbrev withIsolatedMVars {ε α : Type} (action : MetaM (Except ε α)) :
    MetaM (Except ε α) :=
  Morew.Elab.State.withIsolatedMVars action

end Morew.Elab.Affine
