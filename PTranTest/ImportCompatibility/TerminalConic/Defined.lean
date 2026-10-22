import PTran.Reformulation

/-!
# Exported terminal conic artifacts

Nonempty-dimension and positive-margin evidence is needed only by equivalence
proofs. It must survive separate compilation without becoming a decision binder
or an unnecessary parameter of the represented target.
-/

namespace PTranTest.ImportCompatibility.TerminalConic

open PTran PTran.Conic
noncomputable section

class Parameter where
  size : Nat
  epsilon : ℝ

variable [Parameter] (hn : 0 < Parameter.size) (hε : 0 < Parameter.epsilon)

def minimumSource :=
  problem (v : Fin Parameter.size → ℝ) (y t : ℝ)
    minimize t
    subject to
      lse : Fn.logSumExp v ≤ t
      margin : Parameter.epsilon ≤ y
      logarithm : t ≤ Real.log y

include hn hε in
reformulation minimumTarget : minimumSource certificate minimumEquivalence := by
  conic

example : GlobalEquivalence minimumSource minimumTarget :=
  minimumTarget.equivalence hn hε

example : GlobalEquivalence minimumSource minimumTarget := minimumEquivalence hn hε

def maximumSource :=
  problem (y t : ℝ)
    maximize t
    subject to
      margin : Parameter.epsilon ≤ y
      logarithm : t ≤ Real.log y

include hε in
reformulation maximumTarget : maximumSource certificate maximumEquivalence := by
  conic

example : GlobalEquivalence maximumSource maximumTarget := maximumTarget.equivalence hε

end
end PTranTest.ImportCompatibility.TerminalConic
