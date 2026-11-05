# Morew

**Morew** (pronounced “MOH-roo”) is a mathematical optimization rewriting system in Lean 4 for expressing optimization problems and certifying their reformulations.

Morew is under active development.

## Quickstart

Reformulate nonnegative least squares as a second-order cone program:

```lean
import Morew

open Morew
open scoped Matrix

noncomputable def nonnegLS (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm2 (A *ᵥ x - b)
    subject to
      nonneg : x ≥ 0

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

reformulation conicNonnegLS : (nonnegLS A b) := by
  epigraph t as residualBound
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic

noncomputable example : GlobalEquiv (nonnegLS A b) (conicNonnegLS A b) :=
  conicNonnegLS.equiv A b

#printp conicNonnegLS
```

`#printp conicNonnegLS` outputs:

```text
problem (x : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    nonneg : x ∈ ℝ₊^n
    residualCone : (t, A *ᵥ x - b) ∈ SOC m
```

See [Examples](Examples) for more models and reformulations.

## Documentation

Read the [manual](https://dxogrp.github.io/morew/) and
[API reference](https://dxogrp.github.io/morew/api/).

Build and preview the guide, examples, and API reference from the repository root:

```sh
make docs
make preview
```

To publish the current documentation, run the **Documentation deployment** workflow
from `main` after CI passes. Each deployment replaces the previous site.

## License

Morew is licensed under the [Apache License, Version 2.0](LICENSE).
