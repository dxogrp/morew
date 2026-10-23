# Morew

**Morew** (pronounced “MOH-roo”) is a mathematical optimization rewriting system in Lean 4 for expressing optimization problems and certifying their reformulations.

## Example

```lean
import Morew

open Morew
noncomputable section

def original :=
  problem (x : ℝ)
    minimize (Real.log x)^2
    subject to
      positive : 0 < x

reformulation transformed : original := by
  substitute x := Real.exp u
  epigraph t

#check transformed.equivalence
#printp transformed
```

`#printp transformed` outputs:

```text
problem (u t : ℝ)
  minimize t
  subject to
    epigraph_t : u ^ 2 ≤ t
```

## Named components and occurrence bounds

Model-local `let` definitions are available to subsequent definitions, the
objective, and constraints. They may call ordinary Lean functions and use the
problem's parameters and decision variables.

```lean
def regularized :=
  problem (x : ℝ)
    let loss : ℝ := (x - 1) ^ 2
    let penalty := |x|
    minimize loss + penalty
    subject to
      budget : penalty + x ^ 2 ≤ 10

reformulation lifted : regularized := by
  epigraph t at loss as loss_bound
  epigraph a at penalty in budget as abs_bound
  epigraph b at (x ^ 2) in budget
```

The objective becomes `t + penalty`, and `budget` becomes `a + b ≤ 10`.
The definitions remain available, and three constraints record the new upper
bounds. `at loss` selects a direct reference to that definition; `at (expression)`
matches a typed expression. Each selector must match exactly once in the chosen
location. Selection does not unfold definitions, so distinct names with equal
bodies remain distinct targets. Without `in`, selection applies to the objective.

Both `epigraph` and `hypograph` accept modifiers in this order:

```lean
epigraph a at penalty in budget as abs_bound using contextCertificate
```

`in`, `as`, and `using` are optional. `as` names the new bound constraint.
Without `using`, Morew attempts a conservative monotonicity proof. `using`
supplies an explicit, kernel-checked context certificate: for a minimizing
objective, it proves the original objective is at most the lifted objective;
for a maximizing objective, the inequality is reversed. For constraints, the
certificate establishes recovery of the original feasible set after eliminating
the auxiliary variable. It may use other constraints, but cannot assume the row
being replaced. Invalid explicit evidence fails without falling back to automation.

`epigraph` introduces an upper bound and `hypograph` a lower bound. In objectives,
they apply to minimization and maximization respectively. In constraints, the
valid direction depends on the constraint context independently of objective
sense; for example, `1 ≤ x ^ 2` permits a hypograph lift of `x ^ 2`.

See [Examples/Occurrence.lean](Examples/Occurrence.lean) for complete examples
that finish with certified conic conversion.
