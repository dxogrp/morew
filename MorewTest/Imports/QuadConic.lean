/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.QuadConic

assert_not_imported Morew.Elab.NLP.Rewrite
assert_not_imported Morew.Elab.NLP.Terminal
assert_not_imported Morew.Elab.Reformulation.NLP.Terminal

namespace MorewTest.Imports.QuadConic
open Morew
noncomputable section

def source := problem (x : ℝ) minimize (x - 1) ^ 2 subject to bound : |x| ≤ 2
reformulation targeted : source := by conic at bound
reformulation terminal : targeted := by qconic
example : IsQuadConic terminal := terminal.isQuadConic
example : GlobalEquiv source terminal := targeted.equiv.trans terminal.equiv

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 1 do
    Lean.throwError "unexpected quadratic selective-import presentation providers"
  unless (← Lean.Elab.Command.liftCoreM <| Elab.Rewrite.Registry.entries .nlp).isEmpty do
    Lean.throwError "the quadratic entry point installed NLP rules"

end
end MorewTest.Imports.QuadConic
