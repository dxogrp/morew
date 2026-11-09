# Morew

**Morew** (pronounced “MOH-roo”) is a mathematical optimization rewriting system in Lean 4 for expressing optimization problems and certifying their reformulations.

Morew is under active development.
We try our best to keep the API stable, but breaking changes might still occur without notice.

## Installation

Install [Lean through elan](https://lean-lang.org/install/).
Choose a tag from [Releases](https://github.com/dxogrp/morew/releases)
and copy the `lean-toolchain` file from that tag into your project.

Add Morew to your `lakefile.toml`, replacing `<release-tag>` with the chosen tag:

```toml
[[require]]
name = "morew"
git = "https://github.com/dxogrp/morew.git"
rev = "<release-tag>"
```

Then run `lake update`.

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

To build and preview the guide, examples, and API reference from the repository root:

```sh
make docs
make preview
```

## License

Morew is licensed under the [Apache License, Version 2.0](LICENSE).
