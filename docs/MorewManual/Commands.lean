import VersoManual

open Verso.Genre Manual

#doc (Manual) "Commands" =>
%%%
tag := "commands"
file := "commands"
htmlSplit := .never
%%%

Commands act on the current problem and preserve global equivalence. Names in
the syntax below stand for optimization variables, expressions, constraints, or
proofs.

# Epigraphs and hypographs

:::table +header
*
  * Command
  * Effect
*
  * `epigraph t`
  * Replace a minimization objective $`f(x)` by $`t` and add $`f(x)\leq t`.
*
  * `hypograph t`
  * Replace a maximization objective $`f(x)` by $`t` and add $`t\leq f(x)`.
*
  * `epigraph t at expression`
  * Replace a selected expression $`f(x)` by $`t` and add $`f(x)\leq t`.
*
  * `hypograph t at expression`
  * Replace a selected expression $`f(x)` by $`t` and add $`t\leq f(x)`.
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

# Substitution

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

# Constraints

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

# Conic and smooth NLP forms

`conic at label` and `nlp at label` replace one constraint by an equivalent
representation. Append `using rule` to choose its representation explicitly.
These steps may introduce variables and multiple constraints.

A final `conic` or `nlp` command rewrites the remaining constraints, certifies
the target problem, and ends the script. For a reformulation named `q`, it
supplies `q.isConic` or `q.isSmoothNLP`, respectively. These commands are optional;
every reformulation supplies an equivalence certificate.
