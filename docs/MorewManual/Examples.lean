import MorewManual.ExampleSource

open Verso.Genre Manual
open scoped MorewManual.ExampleSource

#doc (Manual) "Examples" =>
%%%
tag := "examples"
file := "examples"
%%%

This chapter presents several examples of applying Morew to rewrite optimization problems.
The examples are ordered according to the learning curve for Morew's features.
Each example includes its Lean source and results.

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

{includeExample Examples.GettingStarted.Basic "Basic modeling"}
{includeExample Examples.GettingStarted.Conic "Conic reformulations"}
{includeExample Examples.GettingStarted.NLP "Smooth nonlinear problems"}
{includeExample Examples.GettingStarted.GraphImpl "Epigraphs and hypographs"}

# Transformations
%%%
tag := "examples-transformations"
%%%

{includeExample Examples.Transformations.Subexpressions "Bounds on subexpressions"}
{includeExample Examples.Transformations.Substitution "Changes of variables"}
{includeExample Examples.Transformations.Rename "Naming constraints"}
{includeExample Examples.Transformations.Derive "Deriving constraints"}
{includeExample Examples.Transformations.Remove "Removing redundant constraints"}

# Models
%%%
tag := "examples-models"
%%%

{includeExample Examples.Models.SecondOrder "Second-order cones"}
{includeExample Examples.Models.Norms "Vector norms"}
{includeExample Examples.Models.Exponential "Exponential cones"}
{includeExample Examples.Models.Power "Power cones"}
{includeExample Examples.Models.PSD "Positive semidefinite matrices"}
{includeExample Examples.Models.Spectral "Eigenvalues and matrix norms"}
{includeExample Examples.Models.LogDet "Log-determinant optimization"}

# Applications
%%%
tag := "examples-applications"
%%%

{includeExample Examples.Applications.Calibration "Multiplicative calibration"}
{includeExample Examples.Applications.RidgeReg "Ridge regression"}

# Advanced
%%%
tag := "examples-advanced"
%%%

{includeExample Examples.Advanced.CustomRules "Custom rules"}
{includeExample Examples.Advanced.Schur "Schur complements"}
{includeExample Examples.Advanced.Restrict "Restricting the feasible set"}
