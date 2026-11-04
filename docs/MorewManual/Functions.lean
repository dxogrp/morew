import VersoManual

open Verso.Genre Manual

#doc (Manual) "Supported functions" =>
%%%
tag := "functions"
file := "functions"
htmlSplit := .never
%%%

A conic formulation has an affine objective and affine maps into cones.
A smooth nonlinear formulation has an objective and scalar residuals that are
twice continuously differentiable on an open domain containing the feasible set.

:::table +header
*
  * Family
  * Assumptions and representations
*
  * Piecewise affine expressions
  * Absolute values, positive parts, and finite minima or maxima. Epigraphs of convex functions and hypographs of concave functions have conic and smooth representations.
*
  * Quadratic and quadratic-over-linear expressions
  * Second-order cones. Quadratic-over-linear expressions require a positive denominator.
*
  * Vector norms
  * Linear, second-order, and power cones. Finite power-cone norms use $`1<p<\infty`. Euclidean bounds also have smooth squared formulations.
*
  * Exponentials and logarithms
  * Exponential cones represent log-sum-exp, softplus, and relative entropy. Logarithms require positive arguments; log-sum-exp uses a nonempty index set; relative entropy requires $`a\geq0` and $`b>0`.
*
  * Powers and means
  * Power cones use $`0<\alpha<1`. Real powers above one use nonnegative bases. Geometric means use nonempty nonnegative vectors; inverse products use nonempty positive vectors. Negative powers use positive bases.
*
  * Matrix constraints
  * Positive semidefiniteness is a native cone constraint. Positive definiteness has a semidefinite block representation.
*
  * Matrix functions
  * Largest eigenvalues use nonempty symmetric matrices; matrix fractions require positive definiteness. Operator and nuclear norms have semidefinite representations.
*
  * Logarithmic determinants
  * Positive-definite matrices; exponential and positive-semidefinite cone representations.
*
  * Smooth expressions
  * Arithmetic, finite sums, exponentials, and trigonometric functions. Logarithms, square roots, and real powers use positive arguments; reciprocals and division use nonzero denominators.
:::

# Conventions

`Fn.norm1`, `Fn.norm2`, and `Fn.normInf` denote $`\lVert x\rVert_1`,
$`\lVert x\rVert_2`, and $`\lVert x\rVert_\infty`.
The native norm of `Fin n → ℝ` is the infinity norm;
`EuclideanSpace` and `WithLp` specify other norms through their types.

Lean defines logarithms, division, and matrix inverses at all inputs; each
representation specifies its domain assumptions. For example,
`Fn.relativeEntropy a b` represents $`a\log(a/b)` for $`a>0` and $`b>0`,
extended to zero at $`a=0`.
The [function API](api/Morew/Fn.html) gives the formulas and dimension conventions.
The [smoothness API](api/Morew/NLP/Smooth.html) and [domain API](api/Morew/NLP/Domain.html)
describe the smooth nonlinear representations.
