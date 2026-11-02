# Morew

**Morew** (pronounced “MOH-roo”) is a mathematical optimization rewriting system in Lean 4 for expressing optimization problems and certifying their reformulations.

Morew is under *active development*.
Features may be broken and/or missing, and the documentation is still incomplete.

## Quickstart

Reformulate nonnegative least squares as a second-order cone program:

```lean
import Morew

open Morew
open scoped Matrix

noncomputable def nonnegLS (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize ‖WithLp.toLp 2 (A *ᵥ x - b)‖
    subject to
      nonneg : x ≥ 0

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

reformulation conicNonnegLS : (nonnegLS A b) := by
  epigraph t as residualBound
  conic at residualBound
  rename residualBound_conic_1 to residualCone
  conic

noncomputable example : GlobalEquivalence (nonnegLS A b) (conicNonnegLS A b) :=
  conicNonnegLS.equivalence A b

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

More examples can be found in the [Examples](Examples) directory.

## License

Morew is licensed under the [Apache License, Version 2.0](LICENSE).
