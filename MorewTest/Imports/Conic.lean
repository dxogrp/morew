/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

assert_not_imported Morew.Elab.NLP.Rewrite
assert_not_imported Morew.Elab.NLP.Terminal
assert_not_imported Morew.Elab.NLP.Rules
assert_not_imported Morew.Elab.Reformulation.NLP.Rewrite
assert_not_imported Morew.Elab.Reformulation.NLP.Terminal

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 1 do
    Lean.throwError "unexpected selective-import presentation providers"

namespace MorewTest.Imports.Conic
open Morew
noncomputable section

def source := problem (x : ℝ) minimize x subject to bound : |x| ≤ 1
reformulation targeted : source := by conic at bound
reformulation terminal : targeted := by conic
example : GlobalEquivalence source terminal := targeted.equivalence.trans terminal.equivalence
example : IsConic terminal := terminal.isConic
example : terminal.conicForm.data.toProblem = terminal := terminal.conicForm.represents

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Elab.Rewrite.Registry.entries .conic
  unless rules.any (·.declaration == ``Rewrite.absEpigraph) do
    Lean.throwError "the selective entry point did not install its default exact rules"
  unless (← Lean.Elab.Command.liftCoreM <| Elab.Rewrite.Registry.entries .nlp).isEmpty do
    Lean.throwError "the selective entry point installed the other backend's rules"

/-- error: reformulation step is unavailable; import Morew.Reformulation.NLP -/
#guard_msgs in
reformulation missingTerminal : source := by nlp
/-- error: reformulation step is unavailable; import Morew.Reformulation.NLP -/
#guard_msgs in
reformulation missingTargeted : source := by nlp at bound
assert_not_exists missingTerminal missingTargeted
end
end MorewTest.Imports.Conic
