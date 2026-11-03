import VersoManual

open Verso.Genre Manual

#doc (Manual) "Custom rules" =>
%%%
tag := "custom-rules"
file := "custom-rules"
htmlSplit := .never
%%%

A custom rule expresses a constraint as an equivalent condition with auxiliary
variables. Define one of these records with `def`:

:::table +header
*
  * Record
  * Source condition
*
  * `GraphRepresentation f`
  * $`y=f(x)`
*
  * `EpigraphRepresentation f`
  * $`f(x)\leq t`
*
  * `HypographRepresentation f`
  * $`t\leq f(x)`
*
  * `ExactConstraintLift P`
  * $`P(x)`
:::

# Required fields

Supply `Auxiliary`, the type of auxiliary values; `target`, the replacement
predicate; and `source_iff_exists`, a proof that the source condition holds
exactly when some auxiliary value satisfies `target`. Use `Unit` when the
replacement needs no auxiliary variable.

For a predicate equivalence $`P(x)\iff Q(x)`, `ExactConstraintLift.ofIff`
constructs the record directly.

# Registration and selection

Register a definition with `@[morew_conic]`, `@[morew_nlp]`, or both.
The corresponding commands select registered rules, infer their parameters
from the selected constraint, and certify the replacement.

Use `conic at label using rule` or `nlp at label using rule` to select a rule
explicitly. The rule may be unregistered.

# Domain assumptions

Express an input domain with a subtype, such as `{x : ℝ // 0 < x}`.
The remaining constraints supply the domain proof required to apply the rule.

The [representation API](api/Morew/Rewrite/Basic.html) gives the record signatures.
