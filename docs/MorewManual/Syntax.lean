import VersoManual

open Verso.Genre Manual

#doc (Manual) "Syntax" =>
%%%
tag := "syntax"
file := "syntax"
htmlSplit := .never
%%%

A problem declaration gives its optimization variables, objective, and constraints.
The following schematic uses functions `r`, `f`, and `c` of the indicated data:

```
def p (a : Parameter) :=
  problem (x : Decision)
    let residual := r a x
    minimize f residual
    subject to
      bound : c a x
```

# Parameters and optimization variables

Arguments before `:=`, such as `a`, are fixed parameters. Binders after
`problem`, such as `x`, are optimization variables. Give each optimization variable an
explicit type; `(x y : ℝ)` declares two variables of the same type. Their types
may depend on parameters, including symbolic dimensions.

# Objectives and constraints

Use `minimize expression` or `maximize expression` to set the objective and its
direction. The indented `subject to` block lists named propositions that must
all hold. Omit the block for an unconstrained problem.

Constraint labels, such as `bound`, identify constraints in later reformulation
steps. A model-local `let name := expression` names an expression for use in
the objective, constraints, or subsequent definitions. It may include a type
annotation, as in `let name : ℝ := expression`.

# Printing

`#print p` displays the type and Lean definition of `p`. The `Problem` structure
contains the fields `objective` and `feasible`.

`#printp p` displays a registered problem's variables, objective, and constraints.
For a problem family, it retains its parameters symbolically. The same command
prints the result of a reformulation.

# Reformulation declarations

A reformulation script applies commands in order to a source problem:

```
reformulation q : p := by
  epigraph t
```

This declares `q` and `q.equivalence`, a certificate of global equivalence with
`p`. Parentheses select an applied problem family:

```
reformulation q : (p a) certificate pq := by
  epigraph t
```

The optional `certificate pq` gives the equivalence certificate the additional
name `pq`. Parameters used from the surrounding Lean context become parameters
of the resulting declarations.
