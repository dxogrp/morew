# Morew

Morew is a Lean 4 library for expressing optimization problems and certifying global reformulations.

## Example

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
