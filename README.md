# Morew

**Morew** (pronounced “MOH-roo”) is a mathematical optimization rewriting system in Lean 4 for expressing optimization problems and certifying their reformulations.

Morew is under *active development*.
Features may be broken and/or missing, and the documentation is still incomplete.

## Quickstart

The following example shows a basic usage of Morew to reformulate a simple optimization problem into an equivalent epigraph form.

More examples can be found in the [Examples](Examples) directory.

```lean
import Morew

open Morew
noncomputable section

def original :=
  problem (x : ℝ)
    minimize (Real.log x)^2
    subject to
      positive : 0 < x

reformulation transformed : original := by
  substitute x := Real.exp u
  epigraph t

#check transformed.equivalence
#printp transformed
```

`#printp transformed` outputs:

```text
problem (u t : ℝ)
  minimize t
  subject to
    epigraph_t : u ^ 2 ≤ t
```

## License

Morew is licensed under the [Apache License, Version 2.0](LICENSE).

Maintained Lean source files in `Morew/`, `MorewTest/`, and `Examples/` begin with this header:

```lean
/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/
```

For new files, use the year the file is introduced. Preserve existing years rather than updating them automatically each year.
