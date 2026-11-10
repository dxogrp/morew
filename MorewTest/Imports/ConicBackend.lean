/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Conic.Terminal

assert_not_imported Morew.Elab.QuadConic.Objective
assert_not_imported Morew.Elab.QuadConic.Form
assert_not_imported Morew.Elab.QuadConic.Terminal
assert_not_imported Morew.Elab.Reformulation.QuadConic.Terminal
assert_not_imported Morew.Elab.NLP.Terminal
assert_not_imported Morew.QuadConic.Basic

assert_not_exists Morew.Elab.QuadConic.reifyObjective Morew.Elab.QuadConic.buildForm

example : Morew.Elab.Conic.Terminal.backend.command = "conic" := rfl
