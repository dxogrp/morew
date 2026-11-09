# Agent instructions

Morew is a Lean 4 library for expressing optimization problems and proving that
their reformulations preserve the intended problem.

## Project layout

- `Morew/`: mathematical definitions, proofs, and elaboration code.
- `MorewTest/`: Lean regression tests.
- `Examples/`: worked examples, also included in the manual.
- `docs/MorewManual/`: the Verso manual.
- `scripts/`: build and release automation; Python tests are in `scripts/tests/`.

## Development

- Keep changes small and focused. Reuse existing definitions and theorems in
  Morew and Mathlib before adding new abstractions.
- Follow the naming, namespaces, imports, and proof style of nearby files.
- Complete proofs without `sorry` or new axioms. State domain assumptions and
  prove the required relations between objectives, feasible points, and recovery
  maps when changing reformulations.
- Keep reusable mathematics in `Morew/` and constructions specific to an example
  in that example.
- Use the pinned toolchain and dependencies. `make update` changes dependencies;
  it is not a build command.

## Examples and documentation

- Write concise, precise English and standard mathematical notation. Avoid slang,
  unnecessary jargon, promotional language, and defensive commentary.
- Follow the notation in Boyd and Vandenberghe's *Convex Optimization* where
  applicable.
- Explain the problem and the mathematical steps in their execution order.
  Use vector and matrix notation where it makes the problem clearer; keep
  coordinate expansions in proofs when possible.
- Keep examples minimal while showing the relevant equivalence and representation
  certificates. Explain non-obvious assumptions and proof steps.
- Edit documentation sources, not generated files under `build/` or `.lake/`.

## Validation

Start with the smallest relevant check. For a Lean module, use
`lake build --wfail <Module>`, for example `lake build --wfail Morew.Fn.Norm`.

For changes to Lean code, finish with the library, test, and example build,
aggregate-import check, and lint checks:

```sh
lake build --wfail Morew MorewTest Examples
make check-imports
lake check-lint
lake lint
```

- When adding, moving, or removing Lean modules, run `make imports` and inspect
  the generated aggregate imports. `make build` also synchronizes them.
- Add regressions to the existing suites for changed behavior and bug fixes.
  Check mathematical properties, certificates, and relevant failure cases.
  Prefer semantic assertions to fixed prose or source-text matching. Keep
  one-off inspections out of permanent tests.
- For automation changes, run
  `python3 -B -m unittest discover -s scripts/tests -v`.
- For manual or example changes, run `make docs-update` and inspect the affected
  pages and navigation in `build/docs/`. It preserves existing API output and
  starts no server. Use `make docs` when the API reference needs rebuilding.
- `make check` and `make check-kernel` additionally run standalone kernel checks;
  they are separate from the routine checks above.
- Choose checks appropriate to the change. A prose-only instruction edit needs
  no Lean build. Repeat successful checks only when further changes warrant it.

## Commits and review

- Preserve unrelated user changes and existing branch history. Rebase or
  force-push only when history rewriting is part of the agreed task.
- Keep commits focused so that mathematical support, elaboration changes,
  examples, and documentation can be reviewed separately where practical.
- Summarize the resulting behavior and the checks performed. State any relevant
  checks that were not run.
