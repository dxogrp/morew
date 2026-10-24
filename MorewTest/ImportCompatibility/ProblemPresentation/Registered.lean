/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax.Presentation

/-!
# Independently registered problem metadata

Register a semantic problem's presentation without the problem elaborator or
printer. Importing this module alongside the DSL producer must retain both sets
of registry entries.
-/

assert_not_exists Morew.elabProblem Morew.elabPrintProblem

namespace MorewTest.ImportCompatibility.ProblemPresentation.Registered

def manual : Morew.Problem Nat Nat where
  objective := id
  feasible _ := True

run_cmd do
  Morew.Syntax.registerProblemView ``manual {
    sense := .minimize
    binders := #[{ name := `m, typeSyntax := Lean.mkIdent `Nat }]
    objective := Lean.mkIdent `m
  }

end MorewTest.ImportCompatibility.ProblemPresentation.Registered
