# PTran

PTran is a Lean 4 library for expressing optimization problems and certifying global reformulations.

## Example

```lean
import PTran

open PTran
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

## Mathematical functions

Models use ordinary Lean and mathlib expressions, including `Real.exp`,
`Real.log`, `Real.sqrt`, `x⁻¹`, `|x|`, `x⁺`, `max x y`, and `min x y`.
User-defined functions and predicates are also valid in a `problem`, and
ordinary Lean theorems and proofs remain available.

Automatic transformations recognize an explicit set of typed operations.
Notation such as `|x|` and the corresponding function call `abs x` share one
internal operation identity. Recognition checks the type and standard mathlib
instances; it does not identify an arbitrary user function by unfolding its
definition or searching for an equivalent expression. An expression can be a
valid part of a model without a particular automatic transformation supporting
it.

Each proof-producing rule owns its domain requirements. For example, the
automatic exponential substitution above requires evidence that the original
variable is positive. Recognizing an operation neither establishes such facts
nor adds constraints.

Recognition leaves the stored source presentation unchanged. `#printp` retains
the spelling used to define a problem; after an explicit transformation,
generated expressions follow Lean's pretty-printing conventions.

Future mathematical convenience functions without a suitable existing mathlib
interface belong under `PTran.Fn`. They will be ordinary Lean definitions,
usable both inside and outside models. Namespace membership alone does not
register a function for automation or certify a transformation. Existing
mathlib functions do not receive duplicate PTran wrappers.
