import VersoManual

open Verso.Genre Manual

#doc (Manual) "Mathematical models" =>
%%%
tag := "models"
file := "models"
%%%

A conic formulation has an affine objective and affine maps into cones.
A smooth nonlinear formulation has a twice continuously differentiable objective
and scalar residuals on an open domain containing every feasible point.

The examples keep alternative formulations beside the same source model.
Each model has a complete `conic` or `nlp` formulation.

:::table +header
*
  * Family
  * Assumptions and representations
  * Examples
*
  * Piecewise affine expressions
  * Absolute values, positive parts, and finite minima or maxima. Conic inequalities use their convex or concave direction; smooth formulations can express their graphs.
  * [Conic](examples/Examples/GettingStarted/Conic/) and [NLP](examples/Examples/GettingStarted/NLP/)
*
  * Least squares; quadratic over linear
  * Second-order cones. The quotient requires a positive denominator.
  * [SecondOrder](examples/Examples/Models/SecondOrder/)
*
  * Vector norms
  * Linear, second-order, and power cones. Finite power-cone norms use $`1<p<\infty`. Euclidean bounds also have smooth squared formulations.
  * [Norms](examples/Examples/Models/Norms/)
*
  * Exponentials and logarithms
  * Exponential cones represent log-sum-exp, softplus, and relative entropy. Log-sum-exp uses a nonempty index set; relative entropy requires $`a\geq0` and $`b>0`.
  * [Exponential](examples/Examples/Models/Exponential/)
*
  * Powers and means
  * Power cones use $`0<\alpha<1`. Real powers above one use nonnegative bases. Geometric means use nonempty nonnegative vectors; inverse products use nonempty positive vectors. Negative powers use positive bases.
  * [Power](examples/Examples/Models/Power/)
*
  * Matrix constraints
  * Positive semidefiniteness is a native cone constraint. Positive definiteness has a semidefinite block representation.
  * [PSD](examples/Examples/Models/PSD/)
*
  * Matrix functions
  * Largest eigenvalues use nonempty symmetric matrices; matrix fractions require positive definiteness. Operator and nuclear norms have semidefinite representations.
  * [Spectral](examples/Examples/Models/Spectral/)
*
  * Logarithmic determinants
  * Positive-definite matrices. Removing a proved domain constraint reduces the example from five constraints to four.
  * [LogDet](examples/Examples/Models/LogDet/)
*
  * Smooth expressions
  * Arithmetic, finite sums, exponentials, and trigonometric functions. Logarithms, square roots, and real powers use positive arguments; reciprocals and division use nonzero denominators.
  * [Smoothness API](api/Morew/NLP/Smooth.html) and [domains](api/Morew/NLP/Domain.html)
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

# Find an example by topic

- Epigraphs, hypographs, and signs: [GraphImpl](examples/Examples/GettingStarted/GraphImpl/) and [Subexpressions](examples/Examples/Transformations/Subexpressions/).
- Vector norms and least squares: [Norms](examples/Examples/Models/Norms/) and [SecondOrder](examples/Examples/Models/SecondOrder/).
- Logarithms and exponentials: [Substitution](examples/Examples/Transformations/Substitution/), [Exponential](examples/Examples/Models/Exponential/), and [LogDet](examples/Examples/Models/LogDet/).
- Powers and means: [Power](examples/Examples/Models/Power/) and [Norms](examples/Examples/Models/Norms/).
- Matrix functions: [PSD](examples/Examples/Models/PSD/), [Spectral](examples/Examples/Models/Spectral/), and [Schur](examples/Examples/Advanced/Schur/).
