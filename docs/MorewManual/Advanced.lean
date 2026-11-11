import VersoManual

open Verso.Genre Manual

#doc (Manual) "Advanced" =>
%%%
tag := "advanced"
file := "advanced"
htmlSplit := .never
%%%

Define custom rules, supply objective certificates, and configure the expansion
of helper functions.

# Custom rules
%%%
tag := "custom-rules"
%%%

A custom rule proves $`P(x)\iff\exists u,\ Q(x,u)`, with source constraint
$`P`, replacement $`Q`, and auxiliary values $`u`. Define it with `def`
using one of these representations:

:::table +header
*
  * Representation
  * Source condition
*
  * `GraphRepr f`
  * $`y=f(x)`
*
  * `EpigraphRepr f`
  * $`f(x)\leq t`
*
  * `HypographRepr f`
  * $`t\leq f(x)`
*
  * `ConstraintRepr P`
  * $`P(x)`
:::

## Required fields

Supply `Auxiliary`, the type of auxiliary values; `target`, the replacement
condition; and `source_iff_exists`, a proof of this equivalence. Use `Unit`
when the replacement needs no auxiliary variable.

For equivalent conditions $`P(x)\iff Q(x)`, `ConstraintRepr.ofIff`
constructs a representation directly.

## Registration and selection

Register a definition with `@[morew_conic]`, `@[morew_nlp]`, or both.
The corresponding commands select registered rules, infer their parameters
from the selected constraint, and certify the replacement.
The `qconic` command uses the same constraint rules as `conic`.

Use `conic at label using rule` or `nlp at label using rule` to select a rule
explicitly. The rule may be unregistered.

## Domain assumptions

Express an input domain with a subtype, such as `{x : ℝ // 0 < x}`.
The remaining constraints supply the domain proof required to apply the rule.

The [representation API](api/Morew/Rewrite/Basic.html) lists the definitions.

# Objective certificates
%%%
tag := "objective-certificates"
%%%

Supply an objective certificate when automatic recognition cannot establish
its representation:

:::table +header
*
  * Command and direction
  * Certificate type
*
  * `conic using cert`, either direction
  * `Affine.Certified f`
*
  * `qconic using cert`, minimization
  * `QuadConic.CertifiedMin f`
*
  * `qconic using cert`, maximization
  * `QuadConic.CertifiedMax f`
:::

Here $`f` is the current objective. An affine certificate represents $`f`
by an affine map. A quadratic certificate proves $`f=Q+a`, where $`Q` is a
homogeneous quadratic form and $`a` is affine, including the constant term.
It also proves $`Q(x)\geq 0` for minimization or $`Q(x)\leq 0` for maximization
throughout the decision space. Zero quadratic parts are allowed.

`QuadConic.CertifiedExpr f` records the decomposition without a curvature proof.
Constraints are converted automatically.

# Options
%%%
tag := "options"
%%%

The `morew.affine`, `morew.quadConic`, and `morew.smooth` options control expansion
of eligible transparent helpers during affine, quadratic, and smoothness
certification, respectively. Each uses the following limits per source expression:

:::table +header
*
  * Option suffix
  * Default
  * Meaning
*
  * `maxExpansionDepth`
  * `32`
  * Maximum number of nested helper expansions.
*
  * `maxExpansionSteps`
  * `1024`
  * Maximum number of helper unfoldings.
*
  * `maxExpansionNodes`
  * `100000`
  * Maximum cumulative expression size, including repeated arguments and intermediate expressions.
:::

Place `set_option morew.affine.maxExpansionDepth 64 in` immediately before a
reformulation to change the affine expansion depth. Use
`morew.quadConic.maxExpansionDepth` for quadratic certification and
`morew.smooth.maxExpansionDepth` for smoothness certification.
The other options have the same scope. Setting any limit to zero disables
helper expansion while retaining direct recognition of supported expressions.
