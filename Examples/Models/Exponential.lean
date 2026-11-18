/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic

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

@[expose] public section

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
The entropy of a probability vector `x ∈ ℝⁿ` is

```math
H(x)=-\sum_{i=1}^{n}x_i\log x_i,
```

with each term defined as zero at `xᵢ = 0`. Consider the problem

```math
\begin{array}{ll}
\text{maximize} & H(x) \\
\text{subject to} & \mathbf{1}^T x=1, \quad x\succeq0.
\end{array}
```

Introduce a scalar lower bound `s ≤ H(x)`. The finite-sum hypograph
representation introduces `t ∈ ℝⁿ` satisfying

```math
\begin{gathered}
s\leq\mathbf{1}^T t, \\
(t_i,x_i,1)\in\mathrm{EXP},\qquad i=1,\ldots,n.
\end{gathered}
```

The resulting problem maximizes `s`. Its backward map recovers `x` by discarding
the bound and auxiliary variables.
-/

namespace Entropy
noncomputable section

def p (n : ℕ) :=
  problem (x : Fin n → ℝ)
    maximize ∑ i, Fn.entr (x i)
    subject to
      domain : 0 ≤ x
      mass : ∑ i, x i = 1

variable (n : ℕ)

reformulation entropyConic : (p n) := by
  hypograph s as entropyBound
  conic

#printp entropyConic
example : GlobalEquiv (p n) (entropyConic n) := entropyConic.equiv n
example : IsConic (entropyConic n) := entropyConic.isConic n
example : (entropyConic.conicForm n).data.toProblem = entropyConic n :=
  (entropyConic.conicForm n).represents

example (z : FeasiblePoint (entropyConic n)) :
    ((entropyConic.equiv n).backward.map z).val = z.val.1.1 := rfl

end
end Entropy

/-!
For a fixed positive reference vector `q ∈ ℝⁿ₊₊` and `x ∈ ℝⁿ₊`, the generalized
KL divergence is

```math
D_{\mathrm{KL}}(x,q)=\sum_{i=1}^{n}\bigl(x_i\log(x_i/q_i)-x_i+q_i\bigr).
```

A zero entry of `x` contributes `qᵢ`. Fit a probability vector `x` to `q` by solving

```math
\begin{array}{ll}
\text{minimize} & D_{\mathrm{KL}}(x,q) \\
\text{subject to} & \mathbf{1}^T x=1, \quad x\succeq0.
\end{array}
```

Introduce a scalar upper bound `D_KL(x,q) ≤ s`. The finite-sum epigraph
representation introduces `t ∈ ℝⁿ` satisfying

```math
\begin{gathered}
\mathbf{1}^T t\leq s, \\
(q_i-x_i-t_i,x_i,q_i)\in\mathrm{EXP},\qquad i=1,\ldots,n.
\end{gathered}
```

The resulting problem minimizes `s`. Its backward map recovers the probability
vector `x`.
-/

namespace KullbackLeibler
noncomputable section

def p (q : Fin n → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize ∑ i, Fn.klDiv (x i) (q i)
    subject to
      domain : 0 ≤ x
      mass : ∑ i, x i = 1

variable (q : Fin n → ℝ) (hq : ∀ i, 0 < q i)

reformulation klConic : (p q) := by
  epigraph s as divergenceBound
  conic

#printp klConic
example : GlobalEquiv (p q) (klConic q) := klConic.equiv q hq
example : IsConic (klConic q) := klConic.isConic q
example : (klConic.conicForm q).data.toProblem = klConic q :=
  (klConic.conicForm q).represents

example (z : FeasiblePoint (klConic q)) :
    ((klConic.equiv q hq).backward.map z).val = z.val.1.1 := rfl

end
end KullbackLeibler

end Examples.Models.Exponential
