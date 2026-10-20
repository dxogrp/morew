import PTran.Elab.Reformulation.Presentation

/-!
# Typed-presentation import isolation

Typed presentations share the semantic objective sense without pulling in source
presentation metadata, problem elaboration, or the surface printer.
-/

assert_not_exists PTran.Syntax.ProblemView PTran.elabProblem PTran.elabPrintProblem

namespace PTranTest.ImportCompatibility.TypedPresentation

open Lean Lean.Meta
open PTran.Elab.Reformulation

def naturalPresentation : PresentationState where
  sense := PTran.ObjectiveSense.minimize
  domainType := mkConst ``Nat
  valueType := mkConst ``Nat
  binders := #[{ name := `n, type := mkConst ``Nat }]
  objective := .lam `n (mkConst ``Nat) (.bvar 0) .default

example : naturalPresentation.sense = PTran.ObjectiveSense.minimize := rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  let canonical ← naturalPresentation.canonicalProblem
  check canonical
  let expectedType ← mkAppM ``PTran.Problem #[mkConst ``Nat, mkConst ``Nat]
  unless ← isDefEq (← inferType canonical) expectedType do
    throwError "the typed-presentation import did not construct a semantic problem"

end PTranTest.ImportCompatibility.TypedPresentation
