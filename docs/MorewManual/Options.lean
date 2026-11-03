import VersoManual

open Verso.Genre Manual

#doc (Manual) "Options" =>
%%%
tag := "options"
file := "options"
htmlSplit := .never
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
