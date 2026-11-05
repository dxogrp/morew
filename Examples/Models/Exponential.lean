/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

open Morew

/-!
# Exponential-cone examples

Relative entropy and softplus have exponential-cone representations.
The relative entropy model has scalar variables `a` and `b`:

```math
\begin{array}{ll}
\text{minimize} & a\log(a/b) \\
\text{subject to} & a \geq 0, \quad b \geq 1.
\end{array}
```

The objective is defined by continuity as zero at `a = 0`.
-/

namespace Examples.Models.Exponential

namespace RelativeEntropy
noncomputable section

def p :=
  problem (a b : ℝ)
    minimize Fn.relativeEntropy a b
    subject to
      numerator : 0 ≤ a
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

/-!
The softplus model has scalar variable `x`:

```math
\begin{array}{ll}
\text{minimize} & \log(1+e^x) \\
\text{subject to} & x \geq -2.
\end{array}
```
-/

namespace Softplus
noncomputable section

def p :=
  problem (x : ℝ)
    minimize Fn.softplus x
    subject to
      lower : -2 ≤ x

-- Rewrite the softplus bound explicitly.
reformulation selectedConic : p := by
  epigraph t as loss
  conic at loss
  conic

#printp selectedConic
example : GlobalEquivalence p selectedConic := selectedConic.equivalence
example : IsConic selectedConic := selectedConic.isConic

-- `conic` can also select the softplus rule automatically.
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
