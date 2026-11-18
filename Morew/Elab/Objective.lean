/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/
module

public import Morew.Elab.Evidence
public import Morew.Elab.Reformulation.Presentation

/-! Validate complete real objectives against their typed presentations. -/

public meta section

namespace Morew.Elab

open Lean Lean.Meta

/-- Check completeness, the real codomain, and the objective's declared function type. -/
def checkRealObjective (presentation : Reformulation.PresentationState) : MetaM Unit := do
  for expression in #[presentation.valueType, presentation.domainType, presentation.objective] do
    unless ← Evidence.complete expression do
      throwError "unresolved metavariables or proof placeholders in typed objective"
  unless (← whnf presentation.valueType).isConstOf ``Real do
    throwError "expected a real-valued objective"
  let expected ← mkArrow presentation.domainType presentation.valueType
  unless ← isDefEq (← inferType presentation.objective) expected do
    throwError "objective function does not match its presentation domain and value type"

end Morew.Elab
