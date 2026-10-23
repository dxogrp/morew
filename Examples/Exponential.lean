import Morew

open Morew

/-!
# Exponential-cone examples
-/

namespace Examples.Exponential

namespace RelativeEntropy
noncomputable section

def p :=
  problem (a b : ℝ)
    minimize Fn.relativeEntropy a b
    subject to
      numerator : 0 ≤ a
      -- This retained lower bound certifies the positive domain required by the rewrite.
      denominator : 1 ≤ b

reformulation lowered : p := by
  epigraph t as entropyBound
  conic at entropyBound

#printp p
#printp lowered
example : GlobalEquivalence p lowered := lowered.equivalence

end
end RelativeEntropy

namespace Softplus
noncomputable section

def p :=
  problem (x : ℝ)
    minimize Fn.softplus x
    subject to
      lower : -2 ≤ x

reformulation lowered : p := by
  epigraph t as loss
  conic at loss
  epigraph value as objectiveBound

#printp lowered
example : GlobalEquivalence p lowered := lowered.equivalence

end
end Softplus

end Examples.Exponential
