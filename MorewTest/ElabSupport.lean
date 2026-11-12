/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Elab.Term
import Lean.Elab.SyntheticMVars

/-!
# Test elaboration and metavariable state checks

Shared elaboration checks independent of affine and conic certification.
-/

namespace MorewTest

open Lean Lean.Meta Lean.Elab.Term

/-- Elaborate an input and synthesize pending tasks without requiring a complete term. -/
def elaborateUnchecked (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

/-- Reject incomplete expressions before checking them with the kernel. -/
def checkCompleteWithKernel (expression : Expr) (failureMessage : String) : MetaM Unit := do
  if expression.hasMVar || expression.hasSorry then
    throwError "{failureMessage}"
  checkWithKernel expression

/-- Check expression and universe metavariable allocation counters. -/
def assertMVarCountersUnchanged (before : MetavarContext) (failureMessage : String) : MetaM Unit := do
  let after ← getMCtx
  unless before.mvarCounter == after.mvarCounter && before.lmvarCounter == after.lmvarCounter do
    throwError "{failureMessage}"

/-- Check expression and universe allocation counters and metavariable depth. -/
def assertMVarAllocationStateUnchanged (before : MetavarContext)
    (failureMessage : String) : MetaM Unit := do
  assertMVarCountersUnchanged before failureMessage
  unless before.depth == (← getMCtx).depth do
    throwError "{failureMessage}"

/-- Check allocation counters, depth, and caller expression assignments.
Universe assignments and other caller state require separate checks. -/
def assertExprMVarStateUnchanged (before : MetavarContext) (context : String) : MetaM Unit := do
  assertMVarAllocationStateUnchanged before s!"{context}: scratch metavariable state changed"
  let after ← getMCtx
  for (id, value) in before.eAssignment.toList do
    unless after.eAssignment.find? id == some value do
      throwError "{context}: an existing caller assignment changed"
  for (id, _) in before.decls.toList do
    unless before.eAssignment.contains id || !(after.eAssignment.contains id) do
      throwError "{context}: an unresolved caller metavariable was assigned"

def Affine.elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elaborateUnchecked term
  if expression.hasSorry || expression.hasMVar then
    throwError "test input did not fully elaborate: {expression}"
  return expression

end MorewTest
