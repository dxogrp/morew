import VersoManual

open Verso.Genre Manual

#doc (Manual) "Advanced" =>
%%%
tag := "advanced"
file := "advanced"
htmlSplit := .never
%%%

# Custom rules

Define a `GraphRepresentation`, `EpigraphRepresentation`,
`HypographRepresentation`, or `ExactConstraintLift` by giving an auxiliary type,
a target predicate, and the existential equivalence. These records are defined
with `def`. Register them with `@[morew_conic]` or `@[morew_nlp]`, or choose a
rule explicitly with `using`.

Domain conditions can be expressed by a subtype; the current constraints supply
the required proof.

# Schur complements

For positive-definite $`A`, the condition $`tI-B^T A^{-1}B\succeq0` is equivalent
to positive semidefiniteness of the block matrix
$`\begin{pmatrix}A&B\\B^T&tI\end{pmatrix}`.
This equivalence gives a constraint representation for `conic at`.

# Restrictions

Adding a restriction can change the feasible set while preserving global optima
through a suitable map of feasible points.
Representative maps can replace a coordinate by its absolute value, sort
interchangeable variables, or select a square-root branch after substitution.
Each map must preserve feasibility and give an objective at least as good.

# Helper-function options

Transparent helper functions are expanded during affine certification.
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
