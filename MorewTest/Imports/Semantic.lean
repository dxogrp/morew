/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Core
import Morew.Transform
import Morew.Conic
import Morew.QuadConic
import Morew.NLP
import Morew.Fn
import Morew.Elab.Rewrite.Registry

assert_not_imported Morew.Elab.Reformulation.Command
assert_not_imported Morew.Elab.Reformulation.Registry
assert_not_imported Morew.Reformulation.Basic
assert_not_imported Morew.Reformulation.Conic
assert_not_imported Morew.Reformulation.NLP
assert_not_imported Morew.Elab.Cone.Plan
assert_not_imported Morew.Elab.Cone.Terminal
assert_not_imported Morew.Elab.Conic.Objective
assert_not_imported Morew.Elab.Conic.Form
assert_not_imported Morew.Elab.Conic.Terminal
assert_not_imported Morew.Elab.QuadConic.Objective
assert_not_imported Morew.Elab.QuadConic.Form
assert_not_imported Morew.Elab.QuadConic.Terminal
assert_not_imported Morew.Elab.Cone.Rules
assert_not_imported Morew.Elab.Reformulation.Cone.Rewrite
assert_not_imported Morew.Elab.Reformulation.Cone.Terminal
assert_not_imported Morew.Elab.Reformulation.Conic.Terminal
assert_not_imported Morew.Elab.Reformulation.QuadConic.Terminal
assert_not_imported Morew.Elab.Reformulation.Cone.View
assert_not_imported Morew.Elab.NLP.Rewrite
assert_not_imported Morew.Elab.NLP.Terminal
assert_not_imported Morew.Elab.NLP.Rules
assert_not_imported Morew.Elab.Reformulation.NLP.Rewrite
assert_not_imported Morew.Elab.Reformulation.NLP.Terminal

assert_not_exists Morew.elabReformulation

run_cmd do
  for backend in #[Morew.Elab.Rewrite.Registry.Target.conic, .nlp] do
    unless (← Lean.Elab.Command.liftCoreM <| Morew.Elab.Rewrite.Registry.entries backend).isEmpty do
      Lean.throwError "semantic representations installed automatic rewrite rules"
