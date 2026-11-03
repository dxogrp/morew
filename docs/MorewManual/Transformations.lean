import VersoManual

open Verso.Genre Manual

#doc (Manual) "Transformations" =>
%%%
tag := "transformations"
file := "transformations"
htmlSplit := .never
%%%

A `reformulation q : p := by` script defines a new problem `q` and its
`q.equivalence` certificate. Use `(p a)` for an applied problem family.
`certificate name` before `:=` gives the certificate an additional name.

:::table +header
*
  * Command
  * Effect
*
  * `epigraph t`
  * Minimize $`t` with the bound $`f(x)\leq t` on the current objective.
*
  * `hypograph t`
  * Maximize $`t` with $`t\leq f(x)`.
*
  * `epigraph t at expression`
  * Replace the selected expression by an upper bound, using the required monotonicity proof. `hypograph` uses a lower bound.
*
  * `substitute x := expression`
  * Replace a coordinate by a parameterization covering its feasible values.
*
  * `derive label : condition using proof`
  * Add a consequence of current feasibility.
*
  * `rename old to new`
  * Change a constraint's label.
*
  * `remove at label`
  * Remove a duplicate constraint or a supported tautology. Use `using proof` for other consequences of the remaining constraints.
*
  * `restrict label : condition using proof`
  * Add a condition and prove that every feasible point has a representative with an objective at least as good.
*
  * `conic at label` or `nlp at label`
  * Replace a selected constraint by an equivalent representation.
*
  * `conic` or `nlp`
  * Complete the script and certify the entire problem in the chosen form.
:::

An intermediate script already has an equivalence certificate. The final
`conic` or `nlp` command also supplies a certificate for the target form.

# Selecting expressions and proofs

For expression bounds, `at name` selects a model-local `let` expression;
`at (term)` selects an explicit subexpression. Selection defaults to the
objective. Add `in label` to select within a constraint and `as label` to name
the new bound.

`using proof` supplies explicit evidence for a bound or removal.
For `conic at` and `nlp at`, `using rule` chooses a representation.
For substitution, `via rule` chooses a coordinate parameterization;
`using proof` supplies a feasible-surjection certificate for the complete problem.
