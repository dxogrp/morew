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

An objective certificate gives an exact affine or quadratic representation
of the current objective $`f`. Define it with `def` and supply it when
automatic recognition cannot establish this representation:

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

For `Affine.Certified f`, supply `map`, an affine map, and `correct`, a proof
that $`\mathrm{map}(x)=f(x)` for every $`x`.

For a quadratic certificate, supply `quadratic`, a homogeneous quadratic form
$`Q`; `affine`, an affine function $`a` including the constant term; and
`correct`, a proof that $`Q(x)+a(x)=f(x)` for every $`x`.
Also supply `curvature`, a proof that $`Q(x)\geq 0` for minimization or
$`Q(x)\leq 0` for maximization throughout the decision space. Parameter
hypotheses may be used to establish this sign condition. Zero quadratic
parts are allowed.

The [affine API](api/Morew/Affine.html) and
[quadratic API](api/Morew/QuadConic/Objective.html) list the definitions.

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
