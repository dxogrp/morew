/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Affine.Expansion
import Morew.Elab.Expr

/-! Bounded unfolding of transparent helpers in quadratic objectives. -/

/-- Maximum nested helper expansions during quadratic objective certification. -/
register_option morew.quadConic.maxExpansionDepth : Nat := {
  defValue := 32
  descr := "Maximum nested helper expansions during quadratic objective certification"
}

/-- Maximum helper unfoldings shared across a quadratic objective. -/
register_option morew.quadConic.maxExpansionSteps : Nat := {
  defValue := 1024
  descr := "Maximum helper unfoldings during quadratic objective certification"
}

/-- Maximum cumulative expanded size of a quadratic objective. -/
register_option morew.quadConic.maxExpansionNodes : Nat := {
  defValue := 100000
  descr := "Maximum cumulative expanded size during quadratic objective certification"
}

namespace Morew.Elab.QuadConic.Expansion

open Lean Lean.Meta

private def config : MetaM Morew.Elab.Expansion.Config := do
  let options ← getOptions
  return {
    depth := morew.quadConic.maxExpansionDepth.get options
    steps := morew.quadConic.maxExpansionSteps.get options
    nodes := morew.quadConic.maxExpansionNodes.get options
    depthOption := `morew.quadConic.maxExpansionDepth
    stepsOption := `morew.quadConic.maxExpansionSteps
    nodesOption := `morew.quadConic.maxExpansionNodes
    label := "quadratic objective"
  }

/-- Whether helper expansion is enabled for quadratic objectives. -/
def enabled : MetaM Bool := do
  return Morew.Elab.Expansion.enabled (← config)

/-- Expand helpers with a shared budget, retaining operation and instance heads. -/
def prepare (source : Expr) : MetaM Affine.Expansion.Result := do
  Affine.Expansion.prepareWithConfig source
    (fun expression preserve => Expr.reduceStructure expression preserve) (← config)

end Morew.Elab.QuadConic.Expansion
