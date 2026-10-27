/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Automatic

/-!
# Checked polyhedral replacements

The focused polyhedral entry point selects from the shared registry. Explicit
records retain the existing whole-predicate adapter and affine certification.
There is no native-operation fallback after registry removal.
-/

namespace Morew.Elab.Conic.Polyhedral

open Lean Lean.Meta

/-- A checked exact replacement, before presentation names are allocated. -/
abbrev Result := Plan.Result

/-- Plan a registered polyhedral replacement or certify an explicit record. -/
def plan (sourcePredicate : Expr) (rule? : Option Expr := none)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError Result) := do
  let result ← match rule? with
    | some rule => Automatic.planExplicit sourcePredicate rule #[] provider
    | none => Automatic.planUnique sourcePredicate #[] provider ((`Morew.Rewrite).isPrefixOf ·)
  return match result with
    | .ok (.inl result) => .ok result
    | .ok (.inr _) => .error {
        expression := sourcePredicate
        reason := "a polyhedral replacement unexpectedly required retained evidence" }
    | .error error => .error error

end Morew.Elab.Conic.Polyhedral
