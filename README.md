# PTran

PTran is a Lean 4 library for certifying **global** optimization-problem
reformulations.  Its definitions and certificates do not assume convexity, and
the project intentionally contains no numerical solver backend.

The first supported workflow is:

```lean
import PTran

open PTran
noncomputable section

def original :=
  problem (x : ℝ)
    minimize (Real.log x)^2
    subject to
      positive : 0 < x

reformulation certified / transformed : original := by
  substitute x := Real.exp u
  epigraph t

#printp transformed
```

The output is:

```text
minimize t
over (u t : ℝ)
subject to
  epigraph_t : u ^ 2 ≤ t
```

`certified` is a kernel-checked value of type
`GlobalEquivalence original transformed`.  A failed transformation means that
PTran could not certify the requested step; it is not a proof that the two
problems are inequivalent.

## Surface API

Problems use explicitly typed, nondependent variables. `subject to` is
optional, and `maximize` is supported alongside `minimize`:

```lean
def boundedMaximum :=
  problem (x y : ℝ)
    maximize x^2 - y^2
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

reformulation maximumCertified / boundedHypograph : boundedMaximum := by
  hypograph t
```

For an unregistered substitution, pass a `FeasibleSurjection` proving that the
change of variables covers every feasible source point:

```lean
substitute x := φ u using coverage
```

V1 substitutions keep the new variable at the replaced variable's type. The
built-in automatic rule recognizes `Real.exp u` when a single-variable source
has a syntactic `0 < x` constraint and substitution is the first step; other
maps use the explicit certificate form.

## Semantics

`Problem X V` stores only an objective `X → V` and feasibility predicate
`X → Prop`. `GlobalImprovement` is the extensible one-way relation, while
`GlobalEquivalence` contains improvements in both directions. Maximization is
represented through `OrderDual V`.

No convexity premise appears in this core. Nonconvex problems use the same
global feasible-point maps and objective inequalities as convex ones. PTran
does not provide numerical solving, local-optimum preservation, or an automatic
equivalence/non-equivalence decision procedure.

See [DESIGN.md](DESIGN.md) for the precise semantics, supported v1 syntax,
nonconvex policy, and non-goals.

## Development

The repository is pinned to Lean 4.33 and its matching mathlib release.

```text
lake update
lake build
```
