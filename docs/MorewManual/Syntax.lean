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

This declares `q` and `q.equiv`, a certificate of global equivalence with
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

## Conic, quadratic conic, and smooth NLP forms

A conic formulation has an affine objective and affine maps into cones.
A quadratic conic formulation has objective $`Q(x)+a(x)`, where $`Q` is a
homogeneous quadratic form and $`a` is affine, with the same kind of cone
constraints. The affine part includes the constant term; there is no implicit
factor of $`1/2`. The quadratic part is nonnegative for minimization and nonpositive
for maximization on the entire decision space.
A smooth nonlinear formulation has an objective and scalar residuals that are
twice continuously differentiable on an open domain containing the feasible set.

`conic at label` and `nlp at label` replace one constraint by an equivalent
representation. Append `using rule` to choose its representation explicitly.
These steps may introduce variables and multiple constraints.

A final `conic`, `qconic`, or `nlp` command rewrites the remaining constraints,
certifies the target problem, and ends the script. For a reformulation named `q`,
it supplies `q.isConic`, `q.isQuadConic`, or `q.isSmoothNLP`, respectively. These
terminal commands are optional; every reformulation supplies an equivalence certificate.

The `qconic` command preserves the quadratic objective, including constants.
It uses the same constraint conversions as `conic`; those conversions may add
auxiliary variables. Use `conic at label using rule` before `qconic` to select a
constraint representation explicitly.

Supported quadratic objectives combine affine terms, squares of affine scalar
expressions, and squared Euclidean norms of affine vectors using addition,
subtraction, negation, finite sums, and multiplication or division by real coefficients
independent of the decision variables. Curvature is proved globally from parameter
hypotheses; affine coefficients need no sign conditions. Division of a term that
depends on decision variables requires evidence that the divisor is nonzero.

For minimization, `Fn.norm2 (A *ᵥ x - b) ^ 2` is supported, as is its sum with
`weight * Fn.norm2 x ^ 2` under the assumption `0 ≤ weight`, including zero weight.
Use `Fn.norm2` for the Euclidean norm of a value of type `Fin n → ℝ`; the ordinary
norm on that function type is the infinity norm. See {ref "options"}[Options] for
helper expansion and its limits.

A subsequent reformulation can apply `epigraph t` and `conic` to a minimizing
quadratic conic problem, or `hypograph t` and `conic` to a maximizing one, when
the resulting bound has a supported conic representation.

# Certificates
%%%
tag := "certificates"
%%%

## Generated declarations

:::table +header
*
  * Declaration
  * Meaning
*
  * `q.equiv`
  * The global equivalence between the source and `q`.
*
  * `q.conicForm`, `q.quadConicForm`, or `q.nlpForm`
  * A conic, quadratic conic, or smooth NLP representation of `q`, with its proof.
*
  * `q.conicForm.represents`, `q.quadConicForm.represents`, or `q.nlpForm.represents`
  * Equality of the represented problem with `q`, including its objective and feasibility conditions.
*
  * `q.isConic`, `q.isQuadConic`, or `q.isSmoothNLP`
  * A proof that the problem has the corresponding form.
:::

For problem families, apply the generated declaration to the parameters first,
as in `(q.conicForm A b).represents`.
The target data also records whether the objective is minimized or maximized,
accessible as `form.data.sense`. A theorem about a particular direction can
require a hypothesis such as `form.data.sense = .minimize`.

`QuadConic.Form q` has fields `data` and `represents : data.toProblem = q`;
`IsQuadConic q` means that such a form exists. The `qconic` command checks the
stored direction against the problem declaration. The form represents the final
problem on its decision space; `q.equiv` relates it to the source, whose variables
and constraints may differ.

## Global equivalence

For minimization problems $`p` and $`q` with feasible sets $`X_p` and $`X_q`
and real-valued objectives $`f_p` and $`f_q`, a `GlobalEquiv p q` contains maps
$`F:X_p\to X_q` and $`G:X_q\to X_p` satisfying

$$`f_q(F(x))\leq f_p(x)\quad(x\in X_p),\qquad
f_p(G(y))\leq f_q(y)\quad(y\in X_q).`

The problems have the same optimal value, and these maps transfer optimal
solutions in either direction.
Maximization uses the reversed objective order, represented in Lean by `OrderDual`.

Given `e : GlobalEquiv p q` and a proof `hy` that a feasible point of `q`
is optimal, `e.map_isGlobalOptimum_backward hy` proves optimality of its image in
`p`.

See the [core API](api/Morew/Core.html).

## Chaining reformulations

A reformulation can use another reformulation as its source. The following
schematic chains two reformulations and composes their certificates with `.trans`:

```
reformulation q : p := by
  ...

reformulation r : q := by
  ...

example : GlobalEquiv p r :=
  q.equiv.trans r.equiv
```
