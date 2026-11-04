import MorewManual.FunctionSymbols

open Verso.Genre Manual
open MorewManual.FunctionSymbols

#doc (Manual) "Atomic functions" =>
%%%
tag := "functions"
file := "functions"
htmlSplit := .never
%%%

These tables give the mathematical properties of the supported functions on
the stated domains. All inputs are real, and parameters are fixed. Convexity is
joint in the arguments; monotonicity is coordinatewise unless specified otherwise.

Convexity: {functionSymbol convex}[] convex; {functionSymbol concave}[] concave;
{functionSymbol affine}[] affine; {functionSymbol neither}[] neither.
Monotonicity: {functionSymbol increasing}[] nondecreasing;
{functionSymbol decreasing}[] nonincreasing; {functionSymbol notMonotone}[] neither.

# Scalar functions

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
  * $`x\in\mathbb R`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`
*
  * `x⁺`
  * $`\max(x,0)`
  * $`x\in\mathbb R`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `max x y`
  * $`\max(x,y)`
  * $`x,y\in\mathbb R`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `min x y`
  * $`\min(x,y)`
  * $`x,y\in\mathbb R`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * `x ^ 2`
  * $`x^2`
  * $`x\in\mathbb R`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`
*
  * `x ^ 2 / y`
  * $`x^2/y`
  * $`x\in\mathbb R`, $`y>0`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`; {functionSymbol decreasing}[] in $`y`
*
  * `Real.exp x`
  * $`e^x`
  * $`x\in\mathbb R`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `Real.log x`
  * $`\log x`
  * $`x>0`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * `Real.sqrt x`
  * $`\sqrt{x}`
  * $`x\geq0`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.softplus x`](api/Morew/Fn/Exponential.html#Morew.Fn.softplus)
  * $`\log(1+e^x)`
  * $`x\in\mathbb R`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.relativeEntropy x y`](api/Morew/Fn/Exponential.html#Morew.Fn.relativeEntropy)
  * $`x\log(x/y)`
  * $`x\geq0`, $`y>0`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[] in $`y`; {functionSymbol notMonotone}[] in $`x`
:::

Relative entropy has value zero at $`x=0`.

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
  * $`x>0`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[]
*
  * `Real.rpow x p`
  * $`x^p`, $`0<p<1`
  * $`x\geq0`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * `Real.rpow x p`
  * $`x^p`, $`p>1`
  * $`x\geq0`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * `x ^ α * y ^ (1 - α)`
  * $`x^\alpha y^{1-\alpha}`, $`0<\alpha<1`
  * $`x,y\geq0`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
:::

The cases $`p=0` and $`p=1` give the affine functions $`1` and $`x`.

# Vector functions

In this table $`x\in\mathbb R^n` with $`n>0`.
The three named norms also accept empty vectors, with value zero.

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
  * $`x\in\mathbb R^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * [`Fn.norm2 x`](api/Morew/Fn/Norm.html#Morew.Fn.norm2)
  * $`\sqrt{\sum_i x_i^2}`
  * $`x\in\mathbb R^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * [`Fn.normInf x`](api/Morew/Fn/Norm.html#Morew.Fn.normInf)
  * $`\max_i |x_i|`
  * $`x\in\mathbb R^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * `‖WithLp.toLp p x‖`
  * $`(\sum_i |x_i|^p)^{1/p}`
  * $`x\in\mathbb R^n`, $`1<p<\infty`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * `∑ i, x i ^ 2`
  * $`\sum_i x_i^2`
  * $`x\in\mathbb R^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x_i|`
*
  * `(∑ i, x i ^ 2) / y`
  * $`\lVert x\rVert_2^2/y`
  * $`x\in\mathbb R^n`, $`y>0`
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
  * [`Fn.logSumExp x`](api/Morew/Fn/Exponential.html#Morew.Fn.logSumExp)
  * $`\log\sum_i e^{x_i}`
  * $`x\in\mathbb R^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.geoMean x`](api/Morew/Fn/Power.html#Morew.Fn.geoMean)
  * $`(\prod_i x_i)^{1/n}`
  * $`x_i\geq0`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[]
*
  * [`Fn.invProd x`](api/Morew/Fn/Power.html#Morew.Fn.invProd)
  * $`1/\prod_i x_i`
  * $`x_i>0`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[]
:::

The native norm of `Fin n → ℝ` is the infinity norm; `EuclideanSpace` uses
the Euclidean norm. Squared Euclidean norms may also be written `‖x‖ ^ 2`.
For `WithLp`, `p : ℝ≥0∞`; the formula uses `p.toReal`.
For finite extrema, `s` is a `Finset` and `hs : s.Nonempty`.

# Matrix functions

Here $`A` is a real matrix, $`P\succ0` means positive definite, and
$`A\preceq B` means $`B-A` is positive semidefinite.
$`\mathbb S^n` denotes the symmetric $`n\times n` matrices, with $`n>0`.

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
  * $`A\in\mathbb S^n`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] under $`\preceq`
*
  * `‖A‖`
  * $`\sup_{\lVert u\rVert_2\leq1}\lVert Au\rVert_2`
  * $`A\in\mathbb R^{m\times n}`
  * {functionSymbol convex}[]
  * {functionSymbol notMonotone}[]
*
  * [`Fn.nuclearNorm A`](api/Morew/Fn/Matrix.html#Morew.Fn.nuclearNorm)
  * $`\sum_i\sigma_i(A)`
  * $`A\in\mathbb R^{m\times n}`
  * {functionSymbol convex}[]
  * {functionSymbol notMonotone}[]
*
  * [`Fn.matrixFrac x P`](api/Morew/Fn/Matrix.html#Morew.Fn.matrixFrac)
  * $`x^{\mathsf T}P^{-1}x`
  * $`x\in\mathbb R^n`, $`P\succ0`
  * {functionSymbol convex}[]
  * {functionSymbol decreasing}[] in $`P` under $`\preceq`; {functionSymbol notMonotone}[] in $`x`
*
  * [`Fn.logDet P`](api/Morew/Fn/Matrix.html#Morew.Fn.logDet)
  * $`\log\det P`
  * $`P\succ0`
  * {functionSymbol concave}[]
  * {functionSymbol increasing}[] under $`\preceq`
:::

For the matrix norm, use `open scoped Matrix.Norms.L2Operator`.
The numbers $`\sigma_i(A)` are the singular values of $`A`.
`Fn.logDet P` may also be written `Real.log P.det`.

The constraints `P.PosSemidef` and `P.PosDef` express positive semidefiniteness
and positive definiteness. Both define convex sets; see the
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
  * $`x\in\mathbb R`
  * {functionSymbol neither}[]
  * {functionSymbol notMonotone}[]
*
  * `Real.cos x`
  * $`\cos x`
  * $`x\in\mathbb R`
  * {functionSymbol neither}[]
  * {functionSymbol notMonotone}[]
*
  * `Real.sinh x`
  * $`\sinh x`
  * $`x\in\mathbb R`
  * {functionSymbol neither}[]
  * {functionSymbol increasing}[]
*
  * `Real.cosh x`
  * $`\cosh x`
  * $`x\in\mathbb R`
  * {functionSymbol convex}[]
  * {functionSymbol increasing}[] in $`|x|`
*
  * `Real.tanh x`
  * $`\tanh x`
  * $`x\in\mathbb R`
  * {functionSymbol neither}[]
  * {functionSymbol increasing}[]
:::

Smooth nonlinear formulations also support arithmetic and finite sums.
Logarithms, square roots, and general real powers require positive arguments
for smoothness; division requires a nonzero denominator. See the
[smoothness API](api/Morew/NLP/Smooth.html) and [domain API](api/Morew/NLP/Domain.html).
