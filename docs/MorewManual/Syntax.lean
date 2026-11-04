import VersoManual

open Verso.Genre Manual

#doc (Manual) "Syntax" =>
%%%
tag := "syntax"
file := "syntax"
htmlSplit := .never
%%%

# Problem definition

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

Arguments before `:=`, such as `a`, are fixed parameters. Binders after
`problem`, such as `x`, are optimization variables. Give each optimization variable an
explicit type; `(x y : ℝ)` declares two variables of the same type. Their types
may depend on parameters, including symbolic dimensions.

Use `minimize expression` or `maximize expression` to set the objective and its
direction. The indented `subject to` block lists named propositions that must
all hold. Omit the block for an unconstrained problem.

Constraint labels, such as `bound`, identify constraints in later reformulation
steps. A model-local `let name := expression` names an expression for use in
the objective, constraints, or subsequent definitions. It may include a type
annotation, as in `let name : ℝ := expression`.

# Printing

The standard `#print p` command displays the type and Lean definition of `p`.
The `Problem` structure contains the fields `objective` and `feasible`.

The additional `#printp p` command displays a registered problem's variables,
objective, and constraints. For a problem family, it retains its parameters
symbolically. The same command prints the result of a reformulation.

# Reformulation

A reformulation script applies commands in order to a source problem and
preserves global equivalence:

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

We list the reformulation commands in the following sections.
The descriptions here are abstract, while the concrete usage examples can be
found in {ref "examples"}[Examples].

## Epigraphs and hypographs

:::table +header
*
  * Command
  * Effect
*
  * `epigraph t`
  * Replace minimization objective $`f(x)` by $`t` and add $`f(x)\leq t`.
*
  * `hypograph t`
  * Replace maximization objective $`f(x)` by $`t` and add $`t\leq f(x)`.
*
  * `epigraph t at expr`
  * Replace selected expression $`f(x)` by $`t` and add $`f(x)\leq t`.
*
  * `hypograph t at expr`
  * Replace selected expression $`f(x)` by $`t` and add $`t\leq f(x)`.
:::

The selectors and optional clauses are:

- `at name` selects a direct reference to a model-local `let` expression.
- `at (term)` selects an explicit subexpression. Exactly one match is required.
- `in label` selects within that constraint; otherwise selection is within the objective.
- `as label` names the added bound.
- `using proof` supplies the evidence needed for the selected replacement.

The clauses occur in that order:

```
epigraph t at (expression) in constraint as bound using proof
```

Both whole-objective commands also accept `as label`.

## Substitution

`substitute x := expression` replaces the coordinate `x` by a parameterization
covering its feasible values. The expression uses a new variable and may depend
on the other optimization variables.

Use `via rule` to select a coordinate parameterization explicitly, or
`using proof` to supply a `FeasibleSurjection` for the complete current problem:

```
substitute x := expression via rule
substitute x := expression using proof
```

Without either clause, Morew selects a registered rule automatically.

## Constraints

:::table +header
*
  * Command
  * Effect
*
  * `derive label : condition using proof`
  * Add a condition implied by current feasibility.
*
  * `rename old to new`
  * Change a constraint's label.
*
  * `remove at label`
  * Remove a duplicate constraint or a supported tautology.
*
  * `remove at label using proof`
  * Remove a constraint implied by the remaining constraints.
*
  * `restrict label : condition using proof`
  * Add a condition and prove that every feasible point has a representative satisfying it with an objective at least as good.
:::

## Conic and smooth NLP forms

`conic at label` and `nlp at label` replace one constraint by an equivalent
representation. Append `using rule` to choose its representation explicitly.
These steps may introduce variables and multiple constraints.

A final `conic` or `nlp` command rewrites the remaining constraints, certifies
the target problem, and ends the script. For a reformulation named `q`, it
supplies `q.isConic` or `q.isSmoothNLP`, respectively. These terminal commands
are optional; every reformulation supplies an equivalence certificate.
