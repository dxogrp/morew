import MorewManual.ExampleSource

open Verso.Genre Manual
open scoped MorewManual.ExampleSource

#doc (Manual) "Examples" =>
%%%
tag := "examples"
file := "examples"
htmlSplit := .never
%%%

Each example includes its Lean source and printed results.
Read Basic first, then Conic and NLP, followed by Epigraphs and hypographs.

Notation follows [Boyd and Vandenberghe's _Convex Optimization_](https://web.stanford.edu/~boyd/cvxbook/).
Vector inequalities are componentwise; symmetric-matrix inequalities use the semidefinite order.

From the repository root, build all examples or one module:

```
lake build --wfail Examples
lake build --wfail Examples.GettingStarted.Basic
```

After building its dependencies, check a source file directly to see its output:

```
lake env lean Examples/GettingStarted/Basic.lean
```

# Getting started
%%%
tag := "examples-getting-started"
%%%

{includeExample Examples.GettingStarted.Basic "Basic"}
{includeExample Examples.GettingStarted.Conic "Conic"}
{includeExample Examples.GettingStarted.NLP "NLP"}
{includeExample Examples.GettingStarted.GraphImpl "Epigraphs and hypographs"}

# Transformations
%%%
tag := "examples-transformations"
%%%

{includeExample Examples.Transformations.Subexpressions "Subexpressions"}
{includeExample Examples.Transformations.Substitution "Substitution"}
{includeExample Examples.Transformations.Rename "Rename"}
{includeExample Examples.Transformations.Derive "Derive"}
{includeExample Examples.Transformations.Remove "Remove"}

# Models
%%%
tag := "examples-models"
%%%

{includeExample Examples.Models.SecondOrder "SecondOrder"}
{includeExample Examples.Models.Norms "Norms"}
{includeExample Examples.Models.Exponential "Exponential"}
{includeExample Examples.Models.Power "Power"}
{includeExample Examples.Models.PSD "PSD"}
{includeExample Examples.Models.Spectral "Spectral"}
{includeExample Examples.Models.LogDet "LogDet"}

# Advanced
%%%
tag := "examples-advanced"
%%%

{includeExample Examples.Advanced.CustomRules "CustomRules"}
{includeExample Examples.Advanced.Schur "Schur"}
{includeExample Examples.Advanced.Restrict "Restrict"}
