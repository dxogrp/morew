/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Elab.Term
import Lean.Elab.SyntheticMVars

/-!
# Complete elaboration of test inputs

This helper has no dependency on affine or conic certification. Its existing
namespace is retained for test callers.
-/

namespace MorewTest.Affine

open Lean Lean.Meta Lean.Elab.Term

def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  if expression.hasSorry || expression.hasMVar then
    throwError "affine test did not fully elaborate: {expression}"
  return expression

end MorewTest.Affine
