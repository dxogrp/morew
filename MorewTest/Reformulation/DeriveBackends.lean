/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.Derive
import MorewTest.Reformulation.SecondOrderCustom.Fixtures

/-! Integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.Derive

open Morew
noncomputable section

reformulation logarithmConic : transitiveSource := by
  derive margin : 1 ≤ x using marginOfFeasible
  hypograph t as logarithm_bound
  conic

example : GlobalEquivalence transitiveSource logarithmConic := logarithmConic.equivalence
example : IsConic logarithmConic := logarithmConic.isConic
example : logarithmConic.conicForm.data.toProblem = logarithmConic :=
  logarithmConic.conicForm.represents

reformulation absoluteConic : interval := by
  derive abs_bound : |x| ≤ 1 using absoluteBound
  conic at abs_bound
  conic

reformulation absoluteNLP : interval := by
  derive abs_bound : |x| ≤ 1 using absoluteBound
  nlp at abs_bound
  nlp

example : GlobalEquivalence interval absoluteConic := absoluteConic.equivalence
example : GlobalEquivalence interval absoluteNLP := absoluteNLP.equivalence
example : IsConic absoluteConic := absoluteConic.isConic
example : IsSmoothNLP absoluteNLP := absoluteNLP.isSmoothNLP

-- A targeted rewrite changes the current domain by introducing an auxiliary.
reformulation afterAuxiliary : SecondOrderCustom.source := by
  conic at auxiliary using SecondOrderCustom.auxiliaryRule
  derive auxiliary_square : 0 ≤ auxiliary_aux ^ 2 using (by
    intro point _
    exact sq_nonneg point.2)

example : GlobalEquivalence SecondOrderCustom.source afterAuxiliary := afterAuxiliary.equivalence
example (x y u : ℝ) : afterAuxiliary.objective ((x, y), u) = x + y := rfl

section
variable (auxiliary_aux auxiliary_aux_1 : ℝ)

-- Newly introduced operand parameters participate in later generated-name
-- allocation, even though the original source did not depend on them.
reformulation freshenedAuxiliary : SecondOrderCustom.source := by
  derive ambient : auxiliary_aux = auxiliary_aux ∧ auxiliary_aux_1 = auxiliary_aux_1
    using (by intro _ _; exact ⟨rfl, rfl⟩)
  conic at auxiliary using SecondOrderCustom.auxiliaryRule

example : GlobalEquivalence SecondOrderCustom.source
    (freshenedAuxiliary auxiliary_aux auxiliary_aux_1) :=
  freshenedAuxiliary.equivalence auxiliary_aux auxiliary_aux_1

/--
info: problem (x y auxiliary_aux_2 : ℝ)
  minimize x + y
  subject to
    before : Real.exp x ≤ 100
    auxiliary_conic_1 : auxiliary_aux_2 = x
    auxiliary_conic_2 : (y, 1 / 2, ![auxiliary_aux_2]) ∈ RSOC 1
    after : y ≤ 10
    ambient : auxiliary_aux = auxiliary_aux ∧ auxiliary_aux_1 = auxiliary_aux_1
-/
#guard_msgs in
#printp freshenedAuxiliary
end

end
end MorewTest.Reformulation.Derive
