/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Rows
import MorewTest.ElabSupport

assert_not_imported Morew.Elab.Cone.Plan
assert_not_imported Morew.Elab.Cone.Rewrite
assert_not_imported Morew.Elab.Cone.Rules
assert_not_imported Morew.Elab.Cone.Terminal
assert_not_imported Morew.Elab.Conic.Objective
assert_not_imported Morew.Elab.Conic.Form
assert_not_imported Morew.Elab.Conic.Terminal
assert_not_imported Morew.Elab.QuadConic.Objective
assert_not_imported Morew.Elab.QuadConic.Form
assert_not_imported Morew.Elab.QuadConic.Terminal
assert_not_imported Morew.Elab.Reformulation.Cone.Terminal
assert_not_imported Morew.QuadConic.Basic

namespace MorewTest.Imports.ConeRows

open Lean Lean.Meta Lean.Elab.Command

run_cmd liftTermElabM do
  let objective ← MorewTest.Affine.elaborate (← `(fun x : ℝ => x ^ 3))
  let predicate ← MorewTest.Affine.elaborate (← `(fun x : ℝ => 0 ≤ x ∧ x ≤ 2))
  let real := mkConst ``Real
  let presentation : Morew.Elab.Reformulation.PresentationState := {
    sense := .minimize
    domainType := real
    valueType := real
    binders := #[{ name := `x, type := real }]
    objective
    constraints := #[{ name := `bounds, predicate }]
  }
  let .ok rows ← Morew.Elab.Cone.buildRows presentation
    | throwError "row assembly unexpectedly depended on the objective"
  unless rows.count == 2 do throwError "row assembly lost a bound"
  checkWithKernel rows.constraints
  checkWithKernel rows.feasibleIff

end MorewTest.Imports.ConeRows
