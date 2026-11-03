import VersoManual

open Verso.Genre Manual
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "Examples.Models.SecondOrder"

#doc (Manual) "Getting started" =>
%%%
tag := "getting-started"
file := "getting-started"
%%%

# Installation

Install [Lean through elan](https://lean-lang.org/install/) and clone Morew:

```
git clone https://github.com/dxogrp/morew.git
cd morew
lake exe cache get
lake build --wfail
```

The repository's `lean-toolchain` selects Lean 4.33.0. In another Lake project
using that toolchain, add Morew as a dependency and run `lake update`:

```
[[require]]
name = "morew"
git = "https://github.com/dxogrp/morew.git"
rev = "main"
```

Use `import Morew` for the complete package. The smaller command entry points are
`Morew.Reformulation.Basic`, `Morew.Reformulation.Conic`, and
`Morew.Reformulation.NLP`. Import both Conic and NLP when comparing formulations.

# A first problem

Given a matrix $`A` and vector $`b`, minimize $`\lVert Ax-b\rVert_2` subject to
$`x\geq 0`. The matrix and vector are parameters; $`x` is the decision variable.
After importing `Morew.Reformulation.Conic`, use `open Morew` and `open scoped Matrix`.

```anchor nonnegLS
noncomputable def nonnegLS (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm2 (A *ᵥ x - b)
    subject to
      nonneg : x ≥ 0
```

Introduce $`t` with $`\lVert Ax-b\rVert_2\leq t`, rewrite that bound as a
second-order cone constraint, and certify the complete problem. Here `A` and `b`
are variables with the same types as above.

```anchor conicNonnegLS
reformulation conicNonnegLS : (nonnegLS A b) := by
  epigraph t as residualBound
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic
```

The reformulation supplies equivalence and conic certificates:

```anchor nonnegLSCertificate
noncomputable example : GlobalEquivalence (nonnegLS A b) (conicNonnegLS A b) :=
  conicNonnegLS.equivalence A b
example : IsConic (conicNonnegLS A b) := conicNonnegLS.isConic A b
```

```anchor printNonnegLS
/-! Print the conic problem. -/
#printp conicNonnegLS
```

```anchorInfo printNonnegLS
problem (x : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    nonneg : x ∈ ℝ₊^n
    residualCone : (t, A *ᵥ x - b) ∈ SOC m
```

# Reading the examples

Read [Basic](examples/Examples/GettingStarted/Basic/) first, then
[Conic](examples/Examples/GettingStarted/Conic/) and
[NLP](examples/Examples/GettingStarted/NLP/). Continue with
[Epigraphs and hypographs](examples/Examples/GettingStarted/GraphImpl/), which
compares conic and smooth formulations of negative objectives.

Each module is self-contained. From the repository root, build all examples or
one module:

```
lake build --wfail Examples
lake build --wfail Examples.GettingStarted.Basic
```

After building its dependencies, check a source file directly to see its output:

```
lake env lean Examples/GettingStarted/Basic.lean
```
