import Morew.Reformulation.Command

/-! Imported sources with function-valued decisions and retained definitions. -/

namespace MorewTest.Reformulation.FunctionDecisionRecovery.Defined

open Morew
noncomputable section

def source :=
  problem (z : ℝ) (f : ℝ → ℝ)
    let unused := z
    minimize f z
    subject to
      budget : f z + z ≤ 10

def family (offset : ℝ) :=
  problem (x : ℝ) (f : ℝ → ℝ → ℝ) (y : ℝ)
    let loss := f x y
    let unused := x
    minimize loss + offset
    subject to
      budget : f x y ≤ 10

-- Recovery from a generated declaration must preserve the same applications.
reformulation generated : source := by

end
end MorewTest.Reformulation.FunctionDecisionRecovery.Defined
