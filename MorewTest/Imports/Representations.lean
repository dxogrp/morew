/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Polyhedral
import Morew.Conic.SecondOrder.Representations
import Morew.Elab.Rewrite.Registry

assert_not_imported Morew.Elab.Reformulation.Command
assert_not_imported Morew.Elab.Reformulation.Registry
assert_not_imported Morew.Elab.Conic.Plan
assert_not_imported Morew.Elab.Conic.Terminal
assert_not_imported Morew.Elab.Conic.Rules
assert_not_imported Morew.Elab.Reformulation.Conic.Rewrite
assert_not_imported Morew.Elab.Reformulation.Conic.Terminal
assert_not_imported Morew.Elab.Reformulation.Conic.View
assert_not_imported Morew.Elab.NLP.Rewrite
assert_not_imported Morew.Elab.NLP.Terminal
assert_not_imported Morew.Elab.NLP.Rules
assert_not_imported Morew.Elab.Reformulation.NLP.Rewrite
assert_not_imported Morew.Elab.Reformulation.NLP.Terminal

run_cmd do
  for backend in #[Morew.Elab.Rewrite.Registry.Target.conic, .nlp] do
    unless (← Lean.Elab.Command.liftCoreM <| Morew.Elab.Rewrite.Registry.entries backend).isEmpty do
      Lean.throwError "representation definitions installed automatic rewrite rules"
