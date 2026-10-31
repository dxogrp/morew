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

Conic rewriting can reuse epigraph and hypograph rules through real negation.
For example, minimizing `-Real.log x` with a retained positive lower bound uses
`epigraph t` followed by `conic`; maximizing `-‖x‖` uses `hypograph t` followed
by `conic`. The underlying rule's domain and norm instance are still checked.
See [Examples/Negation.lean](Examples/Negation.lean) for both complete models.

## License

Morew is licensed under the [Apache License, Version 2.0](LICENSE).
