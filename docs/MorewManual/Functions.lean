module

public import MorewManual.FunctionSymbols

public section

open Verso.Genre Manual
open MorewManual.FunctionSymbols

#doc (Manual) "Atomic functions" =>
%%%
tag := "functions"
file := "functions"
htmlSplit := .never
%%%

The property tables give mathematical definitions on the stated domains; the
support tables describe the registered reformulations. All inputs are real,
and parameters are fixed. Convexity is
joint in the arguments; monotonicity is coordinatewise unless specified otherwise.

We use the following symbols for convexity and monotonicity.

- Convexity: {functionSymbol convex}[] convex; {functionSymbol concave}[] concave;
{functionSymbol affine}[] affine; {functionSymbol neither}[] neither.
- Monotonicity: {functionSymbol increasing}[] nondecreasing;
{functionSymbol decreasing}[] nonincreasing; {functionSymbol notMonotone}[] neither.

In the support tables, an epigraph represents $`f(x)\leq t`, and a hypograph
represents $`t\leq f(x)`. Neither is a graph representation of $`f(x)=t`.
Replacing a nested occurrence also requires the appropriate context evidence;
see {ref "syntax"}[Syntax].

`conic` and `qconic` use the same constraint rules. Their final certificates
also require affine cone arguments and an affine or quadratic objective,
respectively. The listed rules are selected automatically when their hypotheses
can be established. `using` selects a rule explicitly without removing those
hypotheses.

The NLP column distinguishes exact bound rewrites from smoothness certification
of an expression. Smoothness requires an open domain containing the feasible
set. “No built-in rule” describes the current automation for the stated
expression, not a mathematical impossibility. A total Lean definition may have
values outside the domain of its representation or smoothness theorem.

# Scalar functions

The sets $`\mathbf{R}_+` and $`\mathbf{R}_{++}` contain the nonnegative and
positive real numbers, respectively.

:::table (tag := "functions-scalar") +header
*
  * Lean expression
  * Definition
  * Domain
  * Convexity
  * Monotonicity
*
  * `abs x`
  * $`|x|`
  * $`x\in\mathbf{R}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`
*
  * `x⁺`
  * $`\max(x,0)`
  * $`x\in\mathbf{R}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `max x y`
  * $`\max(x,y)`
  * $`x,y\in\mathbf{R}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `min x y`
  * $`\min(x,y)`
  * $`x,y\in\mathbf{R}`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * `x ^ 2`
  * $`x^2`
  * $`x\in\mathbf{R}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`
*
  * [`Fn.huber M x`](api/Morew/Fn/Huber.html#Morew.Fn.huber)
  * $`\begin{cases}x^2,& |x|\leq M\\2M|x|-M^2,& |x|>M\end{cases}`
  * $`x\in\mathbf{R}`, fixed $`M\geq0`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`
*
  * `x ^ 2 / y`
  * $`x^2/y`
  * $`x\in\mathbf{R}`, $`y\in\mathbf{R}_{++}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`; {functionSymbol decreasing}[] in $`y`
*
  * `Real.exp x`
  * $`e^x`
  * $`x\in\mathbf{R}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `Real.log x`
  * $`\log x`
  * $`x\in\mathbf{R}_{++}`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.entr x`](api/Morew/Fn/Exponential.html#Morew.Fn.entr)
  * $`-x\log x`
  * $`x\in\mathbf{R}_+`
  * {functionSymbol concave}[]
  * {functionSymbol notMonotone}[]
*
  * `Real.sqrt x`
  * $`\sqrt{x}`
  * $`x\in\mathbf{R}_+`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.softplus x`](api/Morew/Fn/Exponential.html#Morew.Fn.softplus)
  * $`\log(1+e^x)`
  * $`x\in\mathbf{R}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.relEntr x y`](api/Morew/Fn/Exponential.html#Morew.Fn.relEntr)
  * $`x\log(x/y)`
  * $`x\in\mathbf{R}_+`, $`y\in\mathbf{R}_{++}`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[] in $`y`; {functionSymbol notMonotone}[] in $`x`
*
  * [`Fn.klDiv x y`](api/Morew/Fn/Exponential.html#Morew.Fn.klDiv)
  * $`x\log(x/y)-x+y`
  * $`x\in\mathbf{R}_+`, $`y\in\mathbf{R}_{++}`
  * {functionSymbol convex}[]
  * {functionSymbol notMonotone}[]
:::

`Fn.entr x` is defined as `Real.negMulLog x`; both have registered conic hypographs.
Entropy and relative entropy have value zero at $`x=0`. KL divergence has value
$`y` at $`x=0` and value zero at $`x=y`; its denominator remains positive.

:::table (tag := "functions-scalar-support") +header
*
  * Lean expression
  * Conic representation
  * NLP support
  * Checked example
*
  * `abs x`
  * [Epigraph](api/Morew/Rewrite/Polyhedral.html#Morew.Rewrite.absEpigraph)
  * Same epigraph rewrite
  * [Nonlinear absolute-value bound](examples/Getting-started/Smooth-nonlinear-problems/)
*
  * `x⁺`
  * [Epigraph](api/Morew/Rewrite/Polyhedral.html#Morew.Rewrite.posEpigraph)
  * Same epigraph rewrite
  * [Polyhedral rules](https://github.com/dxogrp/morew/blob/main/MorewTest/Conic/PolyhedralElab.lean)
*
  * `max x y`
  * [Epigraph](api/Morew/Rewrite/Polyhedral.html#Morew.Rewrite.maxEpigraph)
  * Same epigraph rewrite
  * [Polyhedral rules](https://github.com/dxogrp/morew/blob/main/MorewTest/Conic/PolyhedralElab.lean)
*
  * `min x y`
  * [Hypograph](api/Morew/Rewrite/Polyhedral.html#Morew.Rewrite.minHypograph)
  * Same hypograph rewrite
  * [Minimum in an objective](examples/Getting-started/Smooth-nonlinear-problems/)
*
  * `x ^ 2`
  * [Epigraph](api/Morew/Conic/SecondOrder/Repr.html#Morew.Conic.SecondOrder.squareEpigraph)
  * Smooth polynomial
  * [Squares and quotients](examples/Models/Second-order-cones/)
*
  * `Fn.huber M x`
  * [Epigraph](api/Morew/Conic/SecondOrder/Repr.html#Morew.Conic.SecondOrder.huberEpigraph), $`M\geq0`
  * No built-in rule
  * [Robust regression](examples/Applications/Robust-regression/)
*
  * `x ^ 2 / y`
  * [Epigraph](api/Morew/Conic/SecondOrder/Repr.html#Morew.Conic.SecondOrder.squareDivEpigraph), $`y>0`
  * Smooth for $`y\ne0`
  * [Quadratic-over-linear bound](examples/Models/Second-order-cones/)
*
  * `Real.exp x`
  * [Epigraph](api/Morew/Conic/Exponential/Repr.html#Morew.Conic.Exponential.expEpigraph)
  * [Smooth](api/Morew/NLP/Smooth.html#Morew.NLP.Smooth.exp)
  * [Exponential rules](https://github.com/dxogrp/morew/blob/main/MorewTest/Conic/ExponentialElab.lean)
*
  * `Real.log x`
  * [Hypograph](api/Morew/Conic/Exponential/Repr.html#Morew.Conic.Exponential.logHypograph), $`x>0`
  * [Smooth for $`x>0`](api/Morew/NLP/Domain.html#Morew.NLP.Domain.log)
  * [Inferred domains](https://github.com/dxogrp/morew/blob/main/MorewTest/NLP/Domain.lean)
*
  * `Fn.entr x`, `Real.negMulLog x`
  * [Hypograph](api/Morew/Conic/Exponential/Repr.html#Morew.Conic.Exponential.entrHypograph), $`x\geq0`
  * No built-in rule for these expressions
  * [Entropy](examples/Models/Exponential-cones/)
*
  * `Real.sqrt x`
  * No registered rule
  * [Smooth for $`x>0`](api/Morew/NLP/Domain.html#Morew.NLP.Domain.sqrt)
  * [Positive inputs](https://github.com/dxogrp/morew/blob/main/MorewTest/NLP/Domain.lean), [boundary rejection](https://github.com/dxogrp/morew/blob/main/MorewTest/NLP/DomainFailures.lean)
*
  * `Fn.softplus x`
  * [Epigraph](api/Morew/Conic/Exponential/Repr.html#Morew.Conic.Exponential.softplusEpigraph)
  * Smooth expanded formula
  * [Softplus](examples/Models/Exponential-cones/)
*
  * `Fn.relEntr x y`
  * [Epigraph](api/Morew/Conic/Exponential/Repr.html#Morew.Conic.Exponential.relEntrEpigraph), $`x\geq0`, $`y>0`
  * Smooth expanded formula for $`x,y>0`
  * [Relative entropy](examples/Models/Exponential-cones/)
*
  * `Fn.klDiv x y`
  * [Epigraph](api/Morew/Conic/Exponential/Repr.html#Morew.Conic.Exponential.klDivEpigraph), $`x\geq0`, $`y>0`
  * Smooth expanded formula for $`x,y>0`
  * [KL divergence](examples/Models/Exponential-cones/)
:::

The registered native forms include `Real.log (1 + Real.exp x)` for softplus
and `x * Real.log (x / y)` for relative entropy. The entropy expression
`-x * Real.log x` can be smooth-certified for positive `x`; this does not make
`Fn.entr x` a recognized smooth expression.

The conic rule for `x ^ (1 / 2 : ℝ)` is a real-power hypograph. It does not
register `Real.sqrt x` as an equivalent spelling. Likewise, the square-root
smoothness rule requires $`x>0`, although the property table includes $`x=0`.

# Powers

Here `p` and `α` are real parameters. `Real.rpow x p` can also be written `x ^ p`.

:::table (tag := "functions-powers") +header
*
  * Lean expression
  * Definition
  * Domain
  * Convexity
  * Monotonicity
*
  * `Real.rpow x p`
  * $`x^p`, $`p<0`
  * $`x\in\mathbf{R}_{++}`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[]
*
  * `Real.rpow x p`
  * $`x^p`, $`0<p<1`
  * $`x\in\mathbf{R}_+`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * `Real.rpow x p`
  * $`x^p`, $`p>1`
  * $`x\in\mathbf{R}_+`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `x ^ α * y ^ (1 - α)`
  * $`x^\alpha y^{1-\alpha}`, $`0<\alpha<1`
  * $`x,y\in\mathbf{R}_+`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
:::

The cases $`p=0` and $`p=1` give the affine functions $`1` and $`x`.

:::table (tag := "functions-powers-support") +header
*
  * Lean expression
  * Conic representation
  * NLP support
  * Checked example
*
  * `Real.rpow x p`, $`p<0`
  * [Epigraph](api/Morew/Conic/Power/Repr.html#Morew.Conic.Power.rpowNegativeEpigraph), $`x>0`
  * Smooth for $`x>0`
  * [Negative powers](examples/Models/Power-cones/)
*
  * `Real.rpow x p`, $`0<p<1`
  * [Hypograph](api/Morew/Conic/Power/Repr.html#Morew.Conic.Power.rpowHypograph), $`x\geq0`
  * Smooth for $`x>0`
  * [Fractional powers](examples/Models/Power-cones/)
*
  * `Real.rpow x p`, $`p>1`
  * [Epigraph](api/Morew/Conic/Power/Repr.html#Morew.Conic.Power.rpowEpigraph), $`x\geq0`
  * Smooth for $`x>0`
  * [Positive powers](examples/Models/Power-cones/)
*
  * `Real.rpow x 0`, `Real.rpow x 1`
  * [Epigraphs and hypographs](api/Morew/Conic/Power/Repr.html#Morew.Conic.Power.rpowZeroEpigraph), no base restriction
  * General real-power recognition requires $`x>0`
  * [Affine powers](https://github.com/dxogrp/morew/blob/main/MorewTest/Conic/PowerRules.lean)
*
  * `x ^ α * y ^ (1 - α)`
  * [Hypograph](api/Morew/Conic/Power/Repr.html#Morew.Conic.Power.weightedGeoMeanNotationHypograph), $`x,y\geq0`, $`0<\alpha<1`
  * Smooth for $`x,y>0`
  * [Weighted geometric mean](examples/Models/Power-cones/)
:::

The real-power registrations cover both `Real.rpow x p` and `x ^ p`, including
mixed spellings in the weighted geometric mean. Parameter hypotheses must be
available to the conic rule. NLP smoothness uses
[`Domain.rpow`](api/Morew/NLP/Domain.html#Morew.NLP.Domain.rpow); natural powers
such as `x ^ (2 : ℕ)` instead use the unrestricted polynomial rule.

# Vector functions

In this table $`x\in\mathbf{R}^n` with $`n>0`.
The three named norms and `Fn.sumLargest` also accept empty vectors, with value zero.

:::table (tag := "functions-vector") +header
*
  * Lean expression
  * Definition
  * Domain
  * Convexity
  * Monotonicity
*
  * [`Fn.norm1 x`](api/Morew/Fn/Norm.html#Morew.Fn.norm1)
  * $`\sum_i |x_i|`
  * $`x\in\mathbf{R}^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * [`Fn.norm2 x`](api/Morew/Fn/Norm.html#Morew.Fn.norm2)
  * $`\sqrt{\sum_i x_i^2}`
  * $`x\in\mathbf{R}^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * [`Fn.normInf x`](api/Morew/Fn/Norm.html#Morew.Fn.normInf)
  * $`\max_i |x_i|`
  * $`x\in\mathbf{R}^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * `‖WithLp.toLp p x‖`
  * $`(\sum_i |x_i|^p)^{1/p}`
  * $`x\in\mathbf{R}^n`, $`1<p<\infty`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * `∑ i, x i ^ 2`
  * $`\sum_i x_i^2`
  * $`x\in\mathbf{R}^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * `(∑ i, x i ^ 2) / y`
  * $`\lVert x\rVert_2^2/y`
  * $`x\in\mathbf{R}^n`, $`y\in\mathbf{R}_{++}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`; {functionSymbol decreasing}[] in $`y`
*
  * `s.sup' hs x`
  * $`\max_{i\in s}x_i`
  * $`s\ne\varnothing`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `s.inf' hs x`
  * $`\min_{i\in s}x_i`
  * $`s\ne\varnothing`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.sumLargest k x`](api/Morew/Fn/SumLargest.html#Morew.Fn.sumLargest)
  * $`\sum_{i=1}^{\min(k,n)}x_{[i]}`
  * $`x\in\mathbf{R}^n`, $`k\in\mathbf{N}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.cvar β x`](api/Morew/Fn/Cvar.html#Morew.Fn.cvar)
  * $`\operatorname{CVaR}_{\beta}(x)`
  * $`x\in\mathbf{R}^n`, $`n>0`, $`0\leq\beta<1`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.logSumExp x`](api/Morew/Fn/Exponential.html#Morew.Fn.logSumExp)
  * $`\log\sum_i e^{x_i}`
  * $`x\in\mathbf{R}^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.geoMean x`](api/Morew/Fn/Power.html#Morew.Fn.geoMean)
  * $`(\prod_i x_i)^{1/n}`
  * $`x\in\mathbf{R}_+^n`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.invProd x`](api/Morew/Fn/Power.html#Morew.Fn.invProd)
  * $`1/\prod_i x_i`
  * $`x\in\mathbf{R}_{++}^n`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[]
:::

The native norm of `Fin n → ℝ` is the infinity norm; `EuclideanSpace` uses
the Euclidean norm. Squared Euclidean norms may also be written `‖x‖ ^ 2`.
For `WithLp`, `p : ℝ≥0∞`; the formula uses `p.toReal`.
For finite extrema, `s` is a `Finset` and `hs : s.Nonempty`.
For `Fn.sumLargest`, $`x_{[1]}\geq\cdots\geq x_{[n]}` are the sorted coordinates;
$`k=0` gives zero and $`k\geq n` gives the full sum. Its linear epigraph
representation requires $`k\leq n`.

# Matrix functions

The sets $`\mathbf{S}^n`, $`\mathbf{S}_+^n`, and $`\mathbf{S}_{++}^n` contain
the symmetric, positive semidefinite, and positive definite $`n\times n`
matrices, respectively, with $`n>0`. The order $`A\preceq B` means
$`B-A\in\mathbf{S}_+^n`.

:::table (tag := "functions-matrix") +header
*
  * Lean expression
  * Definition
  * Domain
  * Convexity
  * Monotonicity
*
  * [`Fn.lambdaMax A`](api/Morew/Fn/Matrix.html#Morew.Fn.lambdaMax)
  * $`\lambda_{\max}(A)`
  * $`A\in\mathbf{S}^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] under $`\preceq`
*
  * [`Fn.lambdaMin A`](api/Morew/Fn/Matrix.html#Morew.Fn.lambdaMin)
  * $`\lambda_{\min}(A)`
  * $`A\in\mathbf{S}^n`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[] under $`\preceq`
*
  * `‖A‖`
  * $`\sup_{\lVert u\rVert_2\leq1}\lVert Au\rVert_2`
  * $`A\in\mathbf{R}^{m\times n}`
  * {functionSymbol convex}[]
  * {functionSymbol notMonotone}[]
*
  * [`Fn.normNuc A`](api/Morew/Fn/Matrix.html#Morew.Fn.normNuc)
  * $`\sum_i\sigma_i(A)`
  * $`A\in\mathbf{R}^{m\times n}`
  * {functionSymbol convex}[]
  * {functionSymbol notMonotone}[]
*
  * [`Fn.quadForm x Q`](api/Morew/Fn/Matrix.html#Morew.Fn.quadForm)
  * $`x^TQx`
  * $`x\in\mathbf{R}^n`, fixed $`Q\succeq0`
  * {functionSymbol convex}[]
  * {functionSymbol notMonotone}[]
*
  * [`Fn.matFrac x P`](api/Morew/Fn/Matrix.html#Morew.Fn.matFrac)
  * $`x^T P^{-1}x`
  * $`x\in\mathbf{R}^n`, $`P\in\mathbf{S}_{++}^n`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[] in $`P` under $`\preceq`; {functionSymbol notMonotone}[] in $`x`
*
  * [`Fn.logDet P`](api/Morew/Fn/Matrix.html#Morew.Fn.logDet)
  * $`\log\det P`
  * $`P\in\mathbf{S}_{++}^n`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[] under $`\preceq`
:::

For the matrix norm, use `open scoped Matrix.Norms.L2Operator`.
The numbers $`\sigma_i(A)` are the singular values of $`A`.
`Fn.logDet P` may also be written `Real.log P.det`.
`Fn.quadForm x Q` is defined for every real square `Q` and is zero on empty vectors.

The constraints `P.PosSemidef` and `P.PosDef` express membership in
$`\mathbf{S}_+^n` and $`\mathbf{S}_{++}^n`. Both sets are convex; see the
[matrix constraint API](api/Morew/Conic/PSD.html).

# Other smooth functions

:::table (tag := "functions-smooth") +header
*
  * Lean expression
  * Definition
  * Domain
  * Convexity
  * Monotonicity
*
  * `x⁻¹`
  * $`1/x`
  * $`x\ne0`
  * {functionSymbol convex}[] for $`x>0`; {functionSymbol concave}[] for $`x<0`
  * {functionSymbol decreasing}[] on each half-line
*
  * `Real.sin x`
  * $`\sin x`
  * $`x\in\mathbf{R}`
  * {functionSymbol neither}[]
  * {functionSymbol notMonotone}[]
*
  * `Real.cos x`
  * $`\cos x`
  * $`x\in\mathbf{R}`
  * {functionSymbol neither}[]
  * {functionSymbol notMonotone}[]
*
  * `Real.sinh x`
  * $`\sinh x`
  * $`x\in\mathbf{R}`
  * {functionSymbol neither}[]
  * {functionSymbol increasing}[]
*
  * `Real.cosh x`
  * $`\cosh x`
  * $`x\in\mathbf{R}`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`
*
  * `Real.tanh x`
  * $`\tanh x`
  * $`x\in\mathbf{R}`
  * {functionSymbol neither}[]
  * {functionSymbol increasing}[]
:::

Smooth nonlinear formulations also support arithmetic and finite sums.
Logarithms, square roots, and general real powers require positive arguments
for smoothness; division requires a nonzero denominator. See the
[smoothness API](api/Morew/NLP/Smooth.html) and [domain API](api/Morew/NLP/Domain.html).
