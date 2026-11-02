# Morew

**Morew** (pronounced “MOH-roo”) is a mathematical optimization rewriting system in Lean 4 for expressing optimization problems and certifying their reformulations.

Morew is under *active development*.
Features may be broken and/or missing, and the documentation is still incomplete.

## Quickstart

The following example reformulates nonnegative least squares as a second-order cone program. It minimizes the Euclidean residual norm, which has the same minimizers as its square.

More examples can be found in the [Examples](Examples) directory.

```lean
import Morew

open Morew
open scoped Matrix

noncomputable def leastSquares (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize ‖WithLp.toLp 2 (A *ᵥ x - b)‖
    subject to
      nonneg : x ≥ 0

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

reformulation conicLeastSquares : (leastSquares A b) := by
  epigraph t
  conic

#check conicLeastSquares.equivalence
#printp conicLeastSquares
```

`WithLp.toLp 2` selects the Euclidean norm, and `x ≥ 0` means componentwise nonnegativity. `epigraph t` introduces the bound `‖Ax − b‖₂ ≤ t`; `conic` converts it to a cone constraint and certifies the target form.

`#printp conicLeastSquares` outputs:

```text
problem (x : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    nonneg : x ∈ ℝ₊^n
    epigraph_t_conic_1 : (t, A *ᵥ x - b) ∈ SOC m
```

`conicLeastSquares.equivalence` certifies exact global equivalence with the original problem. This reformulates the problem; it does not invoke a numerical solver.

## License

Morew is licensed under the [Apache License, Version 2.0](LICENSE).
