/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

open Morew

/-!
# Exponential-cone examples

Relative entropy uses a nonnegative numerator and a positive denominator.
Softplus needs no domain constraint; its lower bound defines the feasible set.
Both objectives receive epigraph bounds and complete conic certificates.
-/

namespace Examples.Models.Exponential

namespace RelativeEntropy
noncomputable section

def p :=
  problem (a b : ℝ)
    minimize Fn.relativeEntropy a b
    subject to
      numerator : 0 ≤ a
      -- This retained lower bound certifies the positive domain required by the rewrite.
      denominator : 1 ≤ b

reformulation entropyConic : p := by
  epigraph t as entropyBound
  conic at entropyBound
  conic

#printp p
#printp entropyConic
example : GlobalEquivalence p entropyConic := entropyConic.equivalence
example : IsConic entropyConic := entropyConic.isConic

end
end RelativeEntropy

namespace Softplus
noncomputable section

def p :=
  problem (x : ℝ)
    minimize Fn.softplus x
    subject to
      lower : -2 ≤ x

-- Rewrite the selected epigraph constraint before certifying the whole problem.
reformulation selectedConic : p := by
  epigraph t as loss
  conic at loss
  conic

#printp selectedConic
example : GlobalEquivalence p selectedConic := selectedConic.equivalence
example : IsConic selectedConic := selectedConic.isConic

-- The final `conic` command can also perform the softplus rewrite automatically.
reformulation automaticConic : p := by
  epigraph t as loss
  conic

#printp automaticConic
#check automaticConic.conicForm.data
example : GlobalEquivalence p automaticConic := automaticConic.equivalence
example : automaticConic.conicForm.data.toProblem = automaticConic :=
  automaticConic.conicForm.represents
example : IsConic automaticConic := automaticConic.isConic

end
end Softplus

end Examples.Models.Exponential
