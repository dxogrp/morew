import Morew.Reformulation

/-!
# Exported exponential presentations

Section-local nonempty-index and positive-margin evidence certifies the source
rewrite without becoming extra decision variables. The imported presentation
retains its symbolic dimension, grouped cone row, margin, and generated names.
-/

namespace MorewTest.ImportCompatibility.Exponential

open Morew Morew.Conic
noncomputable section

class Parameter where
  size : Nat
  epsilon : ℝ

variable [Parameter] (hn : 0 < Parameter.size) (hε : 0 < Parameter.epsilon)

def source :=
  problem (v : Fin Parameter.size → ℝ) (y t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp v ≤ t
      margin : Parameter.epsilon ≤ y
      logarithm : t ≤ Real.log y
      remaining : |t| ≤ 5

include hn hε in
reformulation lowered : source := by
  conic at lse
  conic at logarithm

example : GlobalEquivalence source lowered := lowered.equivalence hn hε

end
end MorewTest.ImportCompatibility.Exponential
