/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Elab.Term
import Lean.Elab.SyntheticMVars

/-!
# Checked and unchecked elaboration of test inputs

Shared elaboration checks independent of affine and conic certification.
-/

namespace MorewTest

open Lean Lean.Meta Lean.Elab.Term

/-- Elaborate an input and synthesize pending tasks without requiring a complete term. -/
def elaborateUnchecked (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars expression

def Affine.elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elaborateUnchecked term
  if expression.hasSorry || expression.hasMVar then
    throwError "test input did not fully elaborate: {expression}"
  return expression

end MorewTest
