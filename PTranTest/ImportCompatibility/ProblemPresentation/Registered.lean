import PTran.Syntax.Presentation

/-!
# Independently registered problem metadata

Register a semantic problem's presentation without the problem elaborator or
printer. Importing this module alongside the DSL producer must retain both sets
of registry entries.
-/

assert_not_exists PTran.elabProblem PTran.elabPrintProblem

namespace PTranTest.ImportCompatibility.ProblemPresentation.Registered

def manual : PTran.Problem Nat Nat where
  objective := id
  feasible _ := True

run_cmd do
  PTran.Syntax.registerProblemView ``manual {
    sense := .minimize
    binders := #[{ name := `m, typeSyntax := Lean.mkIdent `Nat }]
    objective := Lean.mkIdent `m
  }

end PTranTest.ImportCompatibility.ProblemPresentation.Registered
