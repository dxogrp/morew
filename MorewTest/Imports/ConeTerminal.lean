/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Cone.Rewrite
import Morew.Elab.Reformulation.Cone.Terminal
import Morew.Elab.Reformulation.Cone.View

assert_not_imported Morew.Elab.Conic.Objective
assert_not_imported Morew.Elab.Conic.Form
assert_not_imported Morew.Elab.Conic.Terminal
assert_not_imported Morew.Elab.QuadConic.Objective
assert_not_imported Morew.Elab.QuadConic.Form
assert_not_imported Morew.Elab.QuadConic.Terminal
assert_not_imported Morew.Elab.Reformulation.Conic.Terminal
assert_not_imported Morew.Elab.Reformulation.QuadConic.Terminal
assert_not_imported Morew.Elab.NLP.Terminal
assert_not_imported Morew.QuadConic.Basic

assert_not_exists Morew.Elab.Conic.reifyObjective Morew.Elab.Conic.buildForm
  Morew.Elab.QuadConic.reifyObjective Morew.Elab.QuadConic.buildForm

run_cmd do
  unless (Morew.Elab.Reformulation.viewAttribute.getValues (← Lean.getEnv)
      `presentation).length == 1 do
    Lean.throwError "shared cone imports duplicated presentation providers"
  let rules ← Lean.Elab.Command.liftCoreM <| Morew.Elab.Rewrite.Registry.entries .conic
  unless (rules.filter (·.declaration == ``Morew.Rewrite.absEpigraph)).size == 1 do
    Lean.throwError "shared cone imports did not install the default exact rule exactly once"
  unless (← Lean.Elab.Command.liftCoreM <| Morew.Elab.Rewrite.Registry.entries .nlp).isEmpty do
    Lean.throwError "shared cone imports installed NLP rules"
