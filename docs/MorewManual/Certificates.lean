import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Examples.GettingStarted.Conic"

#doc (Manual) "Certificates" =>
%%%
tag := "certificates"
file := "certificates"
htmlSplit := .never
%%%

For minimization problems $`p` and $`q` with feasible sets $`X_p` and $`X_q`
and real-valued objectives $`f_p` and $`f_q`, a `GlobalEquivalence p q` contains maps
$`F:X_p\to X_q` and $`G:X_q\to X_p` satisfying

$$`f_q(F(x))\leq f_p(x)\quad(x\in X_p),\qquad
f_p(G(y))\leq f_q(y)\quad(y\in X_q).`

The problems have the same optimal value, and these maps transfer optimal
solutions in either direction.
Maximization uses the reversed objective order, represented in Lean by `OrderDual`.

Given `e : GlobalEquivalence p q` and a proof `hy` that a feasible point of `q`
is optimal, `e.map_isGlobalOptimum_backward hy` proves optimality of its image in
`p`.

# Chaining reformulations

A reformulation can use another reformulation as its source. Here `linearBounds`
rewrites the absolute-value bounds of `p`:

```anchor linearBounds -defSite
reformulation linearBounds : p := by
  conic at magnitude
  epigraph t as distance
  conic at distance
```

Complete conic certification in a second declaration, then compose the certificates:

```anchor conicChain -defSite
reformulation conicProb : linearBounds := by
  conic

example : GlobalEquivalence p conicProb :=
  linearBounds.equivalence.trans conicProb.equivalence
```

# Generated declarations

:::table +header
*
  * Declaration
  * Meaning
*
  * `q.equivalence`
  * The global equivalence between the source and `q`.
*
  * `q.conicForm` or `q.nlpForm`
  * The concrete target data and its representation proof.
*
  * `q.conicForm.represents` or `q.nlpForm.represents`
  * Equality of the represented problem with `q`, including its objective and feasible predicate.
*
  * `q.isConic` or `q.isSmoothNLP`
  * A proof that the problem has the corresponding form.
:::

For problem families, apply the generated declaration to the parameters first,
as in `(q.conicForm A b).represents`.
The target data also records whether the objective is minimized or maximized.

# Mathematical evidence

A constraint representation proves $`P(x)\iff\exists u,\ Q(x,u)`.
Graph, epigraph, and hypograph representations apply this statement to
$`y=f(x)`, $`f(x)\leq t`, and $`t\leq f(x)`.
A substitution proves that its parameterization covers every feasible source
point. A restriction supplies a feasible representative with an objective at
least as good.

See the [core API](api/Morew/Core.html) and
[representation API](api/Morew/Rewrite/Basic.html).
