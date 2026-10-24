/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Presentation

/-!
# Typed-presentation import isolation

Typed presentations share the semantic objective sense without pulling in source
presentation metadata, problem elaboration, or the surface printer.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.elabProblem Morew.elabPrintProblem

namespace MorewTest.ImportCompatibility.TypedPresentation

open Lean Lean.Meta
open Morew.Elab.Reformulation

def naturalPresentation : PresentationState where
  sense := Morew.ObjectiveSense.minimize
  domainType := mkConst ``Nat
  valueType := mkConst ``Nat
  binders := #[{ name := `n, type := mkConst ``Nat }]
  objective := .lam `n (mkConst ``Nat) (.bvar 0) .default

example : naturalPresentation.sense = Morew.ObjectiveSense.minimize := rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  let canonical ← naturalPresentation.canonicalProblem
  check canonical
  let expectedType ← mkAppM ``Morew.Problem #[mkConst ``Nat, mkConst ``Nat]
  unless ← isDefEq (← inferType canonical) expectedType do
    throwError "the typed-presentation import did not construct a semantic problem"

end MorewTest.ImportCompatibility.TypedPresentation
