/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

open Morew

/-!
# Exponential-cone examples

Relative entropy, softplus, entropy, and KL divergence have exponential-cone
representations.
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
    minimize Fn.relEntr a b
    subject to
      numerator : 0 ≤ a
      denominator : 1 ≤ b

reformulation entropyConic : p := by
  epigraph t as entropyBound
  conic at entropyBound
  conic

#printp p
#printp entropyConic
example : GlobalEquiv p entropyConic := entropyConic.equiv
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
example : GlobalEquiv p selectedConic := selectedConic.equiv
example : IsConic selectedConic := selectedConic.isConic

-- `conic` can also select the softplus rule automatically.
reformulation automaticConic : p := by
  epigraph t as loss
  conic

#printp automaticConic
#check automaticConic.conicForm.data
example : GlobalEquiv p automaticConic := automaticConic.equiv
example : automaticConic.conicForm.data.toProblem = automaticConic :=
  automaticConic.conicForm.represents
example : IsConic automaticConic := automaticConic.isConic

end
end Softplus

/-!
For a probability vector `(x,y)`, the entropy maximization problem is

```math
\begin{array}{ll}
\text{maximize} & -x\log x-y\log y \\
\text{subject to} & x,y\geq0, \quad x+y=1.
\end{array}
```

Each entropy term has value zero at zero. Introduce lower bounds `u` and `v`
for the two terms, then replace these bounds by exponential-cone constraints.
The resulting objective is `u + v`.
-/

namespace BinaryEntropy
noncomputable section

def p :=
  problem (x y : ℝ)
    let first := Real.negMulLog x
    let second := Real.negMulLog y
    maximize first + second
    subject to
      firstNonneg : 0 ≤ x
      secondNonneg : 0 ≤ y
      mass : x + y = 1

reformulation entropyConic : p := by
  hypograph u at first as firstBound
  hypograph v at second as secondBound
  conic

#printp entropyConic
example : GlobalEquiv p entropyConic := entropyConic.equiv
example : IsConic entropyConic := entropyConic.isConic
example : entropyConic.conicForm.data.toProblem = entropyConic :=
  entropyConic.conicForm.represents

-- The forward map chooses exact entropy values; recovery keeps the probabilities.
example (z : FeasiblePoint p) :
    (entropyConic.equiv.forward.map z).val =
      ((z.val, Real.negMulLog z.val.1), Real.negMulLog z.val.2) := rfl
example (z : FeasiblePoint entropyConic) :
    (entropyConic.equiv.backward.map z).val = z.val.1.1 := rfl

end
end BinaryEntropy

/-!
Fit a probability vector `(x,y)` to the fixed vector `q = (1/3,2/3)` by minimizing
the KL divergence:

```math
\begin{array}{ll}
\text{minimize} & D_{\mathrm{KL}}((x,y),q) \\
\text{subject to} & x,y\geq0, \quad x+y=1,
\end{array}
\qquad
D_{\mathrm{KL}}(p,q)=\sum_{i=1}^{2}\bigl(p_i\log(p_i/q_i)-p_i+q_i\bigr).
```

The entries of `q` are positive, and a zero entry of `p` contributes `qᵢ`.
Introduce an upper bound for each scalar KL term, then rewrite the bounds as
exponential-cone constraints. The backward map recovers the probability vector.
-/

namespace KullbackLeibler
noncomputable section

def p :=
  problem (x y : ℝ)
    let first := Fn.klDiv x (1 / 3)
    let second := Fn.klDiv y (2 / 3)
    minimize first + second
    subject to
      firstNonneg : 0 ≤ x
      secondNonneg : 0 ≤ y
      mass : x + y = 1

reformulation klConic : p := by
  epigraph u at first as firstBound
  epigraph v at second as secondBound
  conic

#printp klConic
example : GlobalEquiv p klConic := klConic.equiv
example : IsConic klConic := klConic.isConic
example : klConic.conicForm.data.toProblem = klConic :=
  klConic.conicForm.represents

example (z : FeasiblePoint p) :
    (klConic.equiv.forward.map z).val =
      ((z.val, Fn.klDiv z.val.1 (1 / 3)), Fn.klDiv z.val.2 (2 / 3)) := rfl
example (z : FeasiblePoint klConic) :
    (klConic.equiv.backward.map z).val = z.val.1.1 := rfl

end
end KullbackLeibler

end Examples.Models.Exponential
