# Examples

These examples define optimization problems, reformulate them, and use Lean
proofs to relate the resulting problems to the originals. Each module can be
read and checked independently.

## Getting started

Read [Basic](GettingStarted/Basic.lean) first, then
[Conic](GettingStarted/Conic.lean) and [NLP](GettingStarted/NLP.lean).
Continue with [GraphImpl](GettingStarted/GraphImpl.lean) to study epigraphs
and hypographs and compare conic and smooth NLP formulations of each problem.

| Module | What it demonstrates |
| --- | --- |
| [Basic](GettingStarted/Basic.lean) | Problem definitions, parameters, printing, epigraphs, and transferring optimality using an equivalence certificate. |
| [Conic](GettingStarted/Conic.lean) | Linear problems, helper functions, selected constraint rewrites, and complete conic certification. |
| [NLP](GettingStarted/NLP.lean) | Absolute-value and minimum expressions reformulated as smooth nonlinear programs. |
| [GraphImpl](GettingStarted/GraphImpl.lean) | Epigraphs, hypographs, and negation, with conic and smooth NLP formulations of negative-logarithm and negative-norm objectives. |

`#printp` displays the current problem. An intermediate reformulation may
introduce an epigraph, substitute coordinates, or rewrite a selected constraint.
It has an equivalence certificate even when the entire problem has not yet
been certified as conic or smooth.

The commands `conic at label` and `nlp at label` rewrite the selected
constraint. The commands `conic` and `nlp` complete the script and certify the
whole problem. The examples show how to use the generated `.equivalence`,
`.isConic`, and `.isSmoothNLP` proofs. Complete formulations also provide
`.conicForm` or `.nlpForm`; their `.represents` proofs relate the corresponding
data to the resulting problem.

## Transformations

These modules focus on individual operations. Some scripts deliberately stop
at an intermediate formulation to show the effect of that operation.

| Module | What it demonstrates |
| --- | --- |
| [Subexpressions](Transformations/Subexpressions.lean) | Introducing epigraph bounds for selected expressions in objectives and constraints, including named `let` expressions. |
| [Substitution](Transformations/Substitution.lean) | Square, affine, and exponential substitutions, including a coefficient that is another decision variable. |
| [Rename](Transformations/Rename.lean) | Naming constraints before and after reformulation and using the resulting names in later steps. |
| [Derive](Transformations/Derive.lean) | Proving a consequence of feasibility and making it available as a constraint for subsequent steps. |
| [Remove](Transformations/Remove.lean) | Removing duplicate constraints, tautologies, and constraints implied by the remaining ones. |

## Mathematical models

Each source model has a complete conic or smooth NLP formulation. When several
representations are useful, they appear together with the same source model.

| Module | Models and comparisons |
| --- | --- |
| [SecondOrder](Models/SecondOrder.lean) | Nonnegative least squares and a quadratic-over-linear objective with a positive denominator. |
| [Norms](Models/Norms.lean) | Named vector norms, a norm-constrained quadratic objective, finite p-norms, and SOC, power-cone, and smooth NLP representations of a Euclidean bound. |
| [Exponential](Models/Exponential.lean) | Relative entropy and explicit versus automatic softplus reformulation. |
| [Power](Models/Power.lean) | Scalar powers, weighted means, direct power-cone membership, geometric means, and inverse products. |
| [PSD](Models/PSD.lean) | Native positive-semidefinite and positive-definite matrix constraints. |
| [Spectral](Models/Spectral.lean) | Largest eigenvalues, operator norms, nuclear norms, and matrix fractions. |
| [LogDet](Models/LogDet.lean) | Log-determinant maximization, domain constraints, and reducing the number of constraints by removing a proved redundancy. |

## Advanced

These examples construct proofs for custom rules or restrictions. Each proof
appears beside the optimization problem that uses it.

| Module | What it demonstrates |
| --- | --- |
| [CustomRules](Advanced/CustomRules.lean) | Parameterized epigraph rules, registration, explicit rule selection, a custom graph equation, and a rule defined on a restricted domain. |
| [Schur](Advanced/Schur.lean) | Proving and applying a Schur-complement constraint equivalence under a positive-definite hypothesis. |
| [Restrict](Advanced/Restrict.lean) | Choosing a nonnegative point, ordering interchangeable variables, and selecting a square-root branch while preserving global optimization behavior. |

### Helper-function options

The introductory [Conic](GettingStarted/Conic.lean) example uses transparent
helper functions in an affine objective and constraint. The default limits
suffice for that example. Larger expressions can require adjustment of these
options:

| Option | Default | Meaning |
| --- | --- | --- |
| `morew.affine.maxExpansionDepth` | `32` | Maximum number of nested helper expansions. |
| `morew.affine.maxExpansionSteps` | `1024` | Maximum number of helper unfoldings across one source expression. |
| `morew.affine.maxExpansionNodes` | `100000` | Maximum cumulative number of expression nodes during expansion, including repeated arguments and intermediate expressions. |

Place `set_option morew.affine.maxExpansionDepth 64 in` immediately before a
reformulation to change the depth for that command alone. The other options
can be scoped in the same way. Setting any limit to zero disables helper
expansion; direct recognition of affine expressions remains available. These
limits apply separately to each source expression and do not make nonlinear
expressions affine.

## Find an example by topic

| Topic | Examples |
| --- | --- |
| Epigraphs, hypographs, and signs | [GraphImpl](GettingStarted/GraphImpl.lean), [Subexpressions](Transformations/Subexpressions.lean) |
| Vector norms and least squares | [Norms](Models/Norms.lean), [SecondOrder](Models/SecondOrder.lean) |
| Logarithms and exponentials | [GraphImpl](GettingStarted/GraphImpl.lean), [Substitution](Transformations/Substitution.lean), [Exponential](Models/Exponential.lean), [LogDet](Models/LogDet.lean) |
| Powers and means | [Power](Models/Power.lean), [Norms](Models/Norms.lean) |
| Matrix constraints and functions | [PSD](Models/PSD.lean), [Spectral](Models/Spectral.lean), [LogDet](Models/LogDet.lean), [Schur](Advanced/Schur.lean) |
| Constraint manipulation | [Rename](Transformations/Rename.lean), [Derive](Transformations/Derive.lean), [Remove](Transformations/Remove.lean), [Restrict](Advanced/Restrict.lean) |
| Defining a rule or proving a restriction | [CustomRules](Advanced/CustomRules.lean), [Schur](Advanced/Schur.lean), [Restrict](Advanced/Restrict.lean) |

## Check the examples

Run these commands from the repository root. Build the complete collection,
including its dependencies:

```sh
lake build --wfail Examples
```

Build one example and its dependencies:

```sh
lake build --wfail Examples.GettingStarted.Basic
```

After the dependencies have been built, check a source file directly to see
its `#printp` output:

```sh
lake env lean Examples/GettingStarted/Basic.lean
```
