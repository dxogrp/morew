import VersoManual

open Verso.Genre Manual

#doc (Manual) "Advanced" =>
%%%
tag := "advanced"
file := "advanced"
htmlSplit := .never
%%%

Define custom rules and configure the expansion of helper functions.

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

Use `conic at label using rule` or `nlp at label using rule` to select a rule
explicitly. The rule may be unregistered.

## Domain assumptions

Express an input domain with a subtype, such as `{x : ℝ // 0 < x}`.
The remaining constraints supply the domain proof required to apply the rule.

The [representation API](api/Morew/Rewrite/Basic.html) lists the definitions.

# Options
%%%
tag := "options"
%%%

Transparent helper functions are expanded during affine and smoothness
certification. The `morew.affine` and `morew.smooth` options control these
operations separately, with the same limits for each source expression:

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
`morew.smooth.maxExpansionDepth` for smoothness certification.
The other options have the same scope. Setting any limit to zero disables
helper expansion while retaining direct recognition of supported expressions.
