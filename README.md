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

## Development

`make build` builds both the library and the compile-time tests with warnings
treated as errors. `make check` additionally lints the library and replays the
compiled library and test declarations through the kernel. The build is
incremental; linting and kernel replay run on every check.

Make defaults to four Lake/linter workers. Override this with
`make LEAN_NUM_THREADS=8 check`, or set `LEAN_NUM_THREADS` in your environment.
Each Morew compiler process uses one worker, and kernel replay remains serial.
Dependency packages retain their own compiler settings, so this is not a strict
CPU limit for the entire process tree.

For focused work, build individual test modules and their dependencies with,
for example, `LEAN_NUM_THREADS=4 lake build --wfail +MorewTest.NLP.Registry`.

## License

Morew is licensed under the [Apache License, Version 2.0](LICENSE).
