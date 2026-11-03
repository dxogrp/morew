import VersoManual

open Verso.Genre Manual

#doc (Manual) "Mathematical models" =>
%%%
tag := "models"
file := "models"
htmlSplit := .never
%%%

A conic formulation has an affine objective and affine maps into cones.
A smooth nonlinear formulation has a twice continuously differentiable objective
and scalar residuals on an open domain containing every feasible point.

:::table +header
*
  * Family
  * Assumptions and representations
*
  * Piecewise affine expressions
  * Absolute values, positive parts, and finite minima or maxima. Conic inequalities use their convex or concave direction; smooth formulations can express their graphs.
*
  * Least squares; quadratic over linear
  * Second-order cones. The quotient requires a positive denominator.
*
  * Vector norms
  * Linear, second-order, and power cones. Finite power-cone norms use $`1<p<\infty`. Euclidean bounds also have smooth squared formulations.
*
  * Exponentials and logarithms
  * Exponential cones represent log-sum-exp, softplus, and relative entropy. Log-sum-exp uses a nonempty index set; relative entropy requires $`a\geq0` and $`b>0`.
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

`Fn.norm1`, `Fn.norm2`, and `Fn.normInf` denote the one-norm, Euclidean norm,
and infinity norm. The native norm of `Fin n → ℝ` is the infinity norm;
`EuclideanSpace` and `WithLp` specify other norms through their types.

Lean's real logarithm, division, and matrix inverse are total functions.
The assumptions of each representation state where its mathematical equivalence
holds. For example, `Fn.relativeEntropy a b` is $`a\log(a/b)`, with value zero
when $`a=0`; its conic representation uses $`a\geq0` and $`b>0`.
The [function API](api/Morew/Fn.html) gives the formulas and dimension conventions.
The [smoothness API](api/Morew/NLP/Smooth.html) and [domain API](api/Morew/NLP/Domain.html)
describe the smooth nonlinear representations.
