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

## Imports and module layout

Use `import PTran` for the complete library. The narrower, supported entry points
are `PTran.Reformulation` for the problem DSL, reformulation command, and printer,
and `PTran.Elab.Reformulation` for reusable typed-runner APIs without the
reformulation command. Both retain their existing declaration namespaces.

The implementation is organized by responsibility:

```text
PTran/
├── Core.lean                    # Problems and equivalence certificates
├── Syntax.lean                  # Problem DSL, presentation metadata, printer
├── Transform.lean               # Verified mathematical transformations
├── Elab/
│   ├── Reformulation.lean       # Typed-runner entry point
│   └── Reformulation/
│       ├── Names.lean           # Name allocation and declaration preflight
│       ├── Presentation.lean    # Typed presentations, deltas, and rebasing
│       └── Runner.lean          # Step contracts, certificates, and commitment
├── Reformulation.lean           # Surface-command entry point
└── Reformulation/
    ├── Syntax.lean              # Reformulation grammar
    ├── State.lean               # Shared surface state and certificate syntax
    ├── Presentation.lean        # Expression conversion and normalization
    ├── Substitution.lean        # Substitution planning and certificates
    ├── ObjectiveBound.lean      # Epigraph/hypograph planning
    ├── StepRunner.lean          # Typed step validation and commitment
    └── Command.lean             # Dispatch and transactional declaration emission
```

Surface modules depend on the typed runner, which depends on problem syntax and
verified transformations; typed support never imports the reformulation command.
Within the surface layer, step implementations build on shared state/presentation
support, and `Command` assembles them. The child modules and
`PTran.Reformulation.Internal` namespace organize implementation details; prefer
the supported entry points over importing these children directly.

`PTranTest/Surface/` groups end-to-end coverage into `Basic`, `NameResolution`,
`ElaborationContext`, and `Diagnostics`; `PTranTest.Surface` imports all four.
`PTranTest/ImportCompatibility/` tests each narrower entry point independently.
The other topical test modules cover mathematical transformations and runner
behavior.

## Development

`PTran.lean` and `PTranTest.lean` are generated import aggregators. After adding
or moving modules, run `make imports` (which invokes `lake exe mk_all`) instead
of maintaining those import lists by hand. The narrower entry-point wrappers
are maintained explicitly.

Run `make check` for import synchronization, a warning-free build, library lint,
and kernel validation. `make clean` removes this package's build artifacts.
