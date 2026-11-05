/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.NLP

assert_not_imported Morew.Elab.Conic.Plan
assert_not_imported Morew.Elab.Conic.Terminal
assert_not_imported Morew.Elab.Conic.Rules
assert_not_imported Morew.Elab.Reformulation.Conic.Rewrite
assert_not_imported Morew.Elab.Reformulation.Conic.Terminal
assert_not_imported Morew.Elab.Reformulation.Conic.View
assert_not_imported Morew.Conic.PSD.NuclearNorm
assert_not_imported Morew.Conic.PSD.LogDet

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 0 do
    Lean.throwError "unexpected selective-import presentation providers"

namespace MorewTest.Imports.NLP
open Morew
noncomputable section

def source := problem (x : ℝ) minimize x subject to bound : |x| ≤ 1
reformulation targeted : source := by nlp at bound
reformulation terminal : targeted := by nlp
example : GlobalEquiv source terminal := targeted.equiv.trans terminal.equiv
example : IsSmoothNLP terminal := terminal.isSmoothNLP
example : terminal.nlpForm.data.toProblem = terminal := terminal.nlpForm.represents

run_cmd do
  let rules ← Lean.Elab.Command.liftCoreM <| Elab.Rewrite.Registry.entries .nlp
  unless rules.any (·.declaration == ``Rewrite.absEpigraph) do
    Lean.throwError "the selective entry point did not install its default exact rules"
  unless (← Lean.Elab.Command.liftCoreM <| Elab.Rewrite.Registry.entries .conic).isEmpty do
    Lean.throwError "the selective entry point installed the other backend's rules"

/-- error: reformulation step is unavailable; import Morew.Reformulation.Conic -/
#guard_msgs in
reformulation missingTerminal : source := by conic
/-- error: reformulation step is unavailable; import Morew.Reformulation.Conic -/
#guard_msgs in
reformulation missingTargeted : source := by conic at bound
assert_not_exists missingTerminal missingTargeted
end
end MorewTest.Imports.NLP
