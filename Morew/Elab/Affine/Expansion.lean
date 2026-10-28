/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.HelperExpansion

/-!
# Bounded helper expansion for affine certification

Affine recognition retains its eager expansion policy and its own locally
scoped options. The shared engine supplies accounting and structural reduction.
-/

/-- Maximum nested helper expansions; zero disables expansion. -/
register_option morew.affine.maxExpansionDepth : Nat := {
  defValue := 32
  descr := "Maximum nested helper expansions during affine certification (zero disables expansion)"
}

/-- Maximum helper unfoldings shared across branches; zero disables expansion. -/
register_option morew.affine.maxExpansionSteps : Nat := {
  defValue := 1024
  descr := "Maximum helper unfoldings during affine certification (zero disables expansion)"
}

/-- Maximum cumulative expanded expression size; zero disables expansion. -/
register_option morew.affine.maxExpansionNodes : Nat := {
  defValue := 100000
  descr := "Maximum cumulative expanded expression size during affine certification (zero disables expansion)"
}

namespace Morew.Elab.Affine.Expansion

open Lean Lean.Meta

/-- The temporary expression and the number of helper occurrences expanded. -/
structure Result where
  /-- A definitionally equal expression used only for proof construction. -/
  expression : Expr
  /-- Number of helper occurrences expanded, counting repeated applications. -/
  expansions : Nat

private def config : MetaM HelperExpansion.Config := do
  let options ← getOptions
  return {
    depth := morew.affine.maxExpansionDepth.get options
    steps := morew.affine.maxExpansionSteps.get options
    nodes := morew.affine.maxExpansionNodes.get options
    depthOption := `morew.affine.maxExpansionDepth
    stepsOption := `morew.affine.maxExpansionSteps
    nodesOption := `morew.affine.maxExpansionNodes
    label := "affine"
  }

/-- Whether every helper-expansion budget is nonzero. -/
def enabled : MetaM Bool := do
  return HelperExpansion.enabled (← config)

/-- Prepare one source expression with one shared budget. The supplied reducer
handles only existing structural reductions; helper unfolding lives here.
Proof and instance lets remain available to evidence collection and reification.
Zero in any option disables all helper expansion. -/
def prepare (source : Expr) (reduce : Expr → Bool → MetaM Expr) : MetaM Result := do
  let bounds ← config
  match ← HelperExpansion.prepare bounds source reduce with
  | .ok result => return { expression := result.expression, expansions := result.expansions }
  | .error error => throwError error.toMessageData bounds.label

/-- Expand safe helper heads without modifying the source presentation. -/
def expand (source : Expr) (reduce : Expr → Bool → MetaM Expr) : MetaM Expr := do
  return (← prepare source reduce).expression

end Morew.Elab.Affine.Expansion
