/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.QuadConic.Terminal

assert_not_imported Morew.Elab.Conic.Objective
assert_not_imported Morew.Elab.Conic.Form
assert_not_imported Morew.Elab.Conic.Terminal
assert_not_imported Morew.Elab.Reformulation.Conic.Terminal
assert_not_imported Morew.Elab.NLP.Terminal

assert_not_exists Morew.Elab.Conic.reifyObjective Morew.Elab.Conic.buildForm

example : Morew.Elab.QuadConic.Terminal.backend.command = "qconic" := rfl
