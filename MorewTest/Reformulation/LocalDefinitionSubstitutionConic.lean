/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.LocalDefinitionSubstitution

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.LocalDefinitionSubstitution

open Morew
noncomputable section

-- A preserved proof block keeps `log(exp u)` in the source presentation, while
-- terminal conic certification recognizes the checked affine objective `u`.
reformulation proofConic : proofSource := by
  substitute x := Real.exp u
  conic

example : GlobalEquivalence proofSource proofConic := proofConic.equivalence
example : Conic.Form proofConic := proofConic.conicForm
example : proofConic.conicForm.data.toProblem = proofConic :=
  proofConic.conicForm.represents

reformulation fixedSubtypeConic : fixedSubtypeSource := by
  substitute x := Real.exp u
  epigraph t
  conic

example : GlobalEquivalence fixedSubtypeSource fixedSubtypeConic :=
  fixedSubtypeConic.equivalence
example : Conic.Form fixedSubtypeConic := fixedSubtypeConic.conicForm
example : fixedSubtypeConic.conicForm.data.toProblem = fixedSubtypeConic :=
  fixedSubtypeConic.conicForm.represents

end
end MorewTest.Reformulation.LocalDefinitionSubstitution
