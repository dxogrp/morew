/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Substitution.Rules

/-! Imported downstream coordinate rules for registry and replay tests. -/

namespace MorewTest.Substitution.Registry.Source

open Morew

/-- A downstream operation whose mathematical head stays opaque to matching. -/
noncomputable def shift (c u : ℝ) : ℝ := u + c

/-- A registered downstream rule with a retained-coordinate-dependent offset. -/
@[morew_substitute]
noncomputable def shiftRule {R : Type*} (c : R → ℝ) :
    CoordinateParameterization (fun r u => shift (c r) u) where
  range _ _ := True
  preimage r x := x.1 - c r
  rightInverse _ _ := sub_add_cancel _ _

/-- A distinct declaration with identical mathematical behavior. -/
noncomputable def shiftAlias {R : Type*} (c : R → ℝ) :
    CoordinateParameterization (fun r u => shift (c r) u) := shiftRule c

namespace Scoped

/-- A scoped registration using the built-in square map. -/
noncomputable def squareRule {R : Type*} :
    CoordinateParameterization (fun (_ : R) (u : ℝ) => u ^ 2) :=
  Morew.Substitution.square

attribute [scoped morew_substitute] squareRule

end Scoped

end MorewTest.Substitution.Registry.Source
