import Morew.Reformulation.Command

/-! Compiled sources whose direct occurrences would change under beta reduction. -/

namespace MorewTest.Reformulation.OccurrenceStructure.Defined

open Morew
noncomputable section

def family (offset : ℝ) :=
  problem (x : ℝ)
    let loss := (x - offset) ^ 2
    let same := (x - offset) ^ 2
    let unused := x + offset
    minimize (fun y : ℝ => y + y) loss + same
    subject to
      cap : (fun y : ℝ => y + y ≤ 10) loss

section

variable (offset : ℝ)

-- Even emitting an unchanged target must preserve the structure for later steps.
reformulation generated : (family offset) := by

end

end
end MorewTest.Reformulation.OccurrenceStructure.Defined
