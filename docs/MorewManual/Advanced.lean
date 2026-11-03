import VersoManual

open Verso.Genre Manual

#doc (Manual) "Advanced" =>
%%%
tag := "advanced"
file := "advanced"
%%%

# Custom rules

Define a `GraphRepresentation`, `EpigraphRepresentation`,
`HypographRepresentation`, or `ExactConstraintLift` by giving an auxiliary type,
a target predicate, and the existential equivalence. These records are defined
with `def`. Register them with `@[morew_conic]` or `@[morew_nlp]`, or choose a
rule explicitly with `using`.

[CustomRules](examples/Examples/Advanced/CustomRules/) demonstrates parameterized
absolute deviation, an absolute-value graph, and logarithms on a positive domain.
Domain conditions can be expressed by a subtype; the current constraints supply
the required proof.

# Schur complements

For positive-definite $`A`, the condition $`tI-B^T A^{-1}B\succeq0` is equivalent
to positive semidefiniteness of the block matrix
$`\begin{pmatrix}A&B\\B^T&tI\end{pmatrix}`.
[Schur](examples/Examples/Advanced/Schur/) proves a constraint equivalence and
applies its certificate to a model.

# Restrictions

Adding a restriction can change the feasible set while preserving global optima
through a suitable map of feasible points.
[Restrict](examples/Examples/Advanced/Restrict/) develops three examples:
replacing a coordinate by its absolute value, sorting interchangeable variables,
and selecting a square-root branch after substitution.

# Helper-function options

Transparent helper functions are expanded during affine certification.
[Conic](examples/Examples/GettingStarted/Conic/) gives a simple example.
These options bound expansion for each source expression:

:::table +header
*
  * Option
  * Default
  * Meaning
*
  * `morew.affine.maxExpansionDepth`
  * `32`
  * Maximum number of nested helper expansions.
*
  * `morew.affine.maxExpansionSteps`
  * `1024`
  * Maximum number of helper unfoldings.
*
  * `morew.affine.maxExpansionNodes`
  * `100000`
  * Maximum cumulative expression size, including repeated arguments and intermediate expressions.
:::

Place `set_option morew.affine.maxExpansionDepth 64 in` immediately before a
reformulation to change its depth limit. The other options have the same scope.
Setting any limit to zero disables helper expansion; direct affine recognition
remains available.
