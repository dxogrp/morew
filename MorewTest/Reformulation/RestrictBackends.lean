/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP
import MorewTest.Reformulation.Restrict
import MorewTest.Reformulation.SecondOrderCustom.Fixtures

/-! Backend integration cases sharing the generic suite's declarations. -/

namespace MorewTest.Reformulation.Restrict

open Morew
noncomputable section

reformulation absoluteConic : squareLine := by
  restrict abs_cap : |x| ≤ 1 using zeroCapRepair
  conic at abs_cap
  epigraph t as objective_bound
  conic

reformulation absoluteNLP : squareLine := by
  restrict abs_cap : |x| ≤ 1 using zeroCapRepair
  nlp at abs_cap
  nlp

example : GlobalEquivalence squareLine absoluteConic := absoluteConic.equivalence
example : GlobalEquivalence squareLine absoluteNLP := absoluteNLP.equivalence
example : IsConic absoluteConic := absoluteConic.isConic
example : IsSmoothNLP absoluteNLP := absoluteNLP.isSmoothNLP
example : absoluteConic.conicForm.data.toProblem = absoluteConic := absoluteConic.conicForm.represents
example : absoluteNLP.nlpForm.data.toProblem = absoluteNLP := absoluteNLP.nlpForm.represents
example (x : ℝ) : absoluteNLP.feasible x ↔ x ≤ 1 ∧ -x ≤ 1 := Iff.rfl

section
variable (auxiliary_aux auxiliary_aux_1 : ℝ)

-- New operands reserve names before a later consumer allocates an auxiliary.
reformulation freshenedAuxiliary : SecondOrderCustom.source := by
  restrict ambient : auxiliary_aux = auxiliary_aux ∧ auxiliary_aux_1 = auxiliary_aux_1
    using {
      map := fun point => ⟨point.1, ⟨point.2, rfl, rfl⟩⟩
      objective_le := fun _ => le_rfl }
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
end MorewTest.Reformulation.Restrict
