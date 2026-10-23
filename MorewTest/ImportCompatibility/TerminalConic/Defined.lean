import Morew.Reformulation

/-!
# Exported terminal conic artifacts

Nonempty-dimension and positive-margin evidence is needed only by equivalence
proofs. It must survive separate compilation without becoming a decision binder
or an unnecessary parameter of the represented target.
-/

namespace MorewTest.ImportCompatibility.TerminalConic

open Morew Morew.Conic
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

noncomputable section

variable [Parameter]

def dimensionSource :=
  problem (v : Fin Parameter.size → ℝ) (t : ℝ)
    minimize t
    subject to loss : Fn.logSumExp v ≤ t

-- Instance evidence is required by the rewrite's equivalence, but the final
-- conic form and its derived property remain valid for every dimension.
section NonzeroDimension

variable [hne : NeZero Parameter.size]

#guard_msgs in
reformulation nonzeroTarget : dimensionSource := by
  conic

example : GlobalEquivalence dimensionSource nonzeroTarget := nonzeroTarget.equivalence

-- Keep the same instance when the represented problem actually uses it.
def coordinateSource :=
  problem (v : Fin Parameter.size → ℝ)
    minimize v 0
    subject to upper : v 0 ≤ 1

#guard_msgs in
reformulation coordinateTarget : coordinateSource := by
  conic

example : IsConic coordinateTarget := coordinateTarget.isConic

end NonzeroDimension

section NonemptyDimension

variable [hne : Nonempty (Fin Parameter.size)]

#guard_msgs in
reformulation nonemptyTarget : dimensionSource := by
  conic

example : GlobalEquivalence dimensionSource nonemptyTarget := nonemptyTarget.equivalence

end NonemptyDimension

end
end MorewTest.ImportCompatibility.TerminalConic
