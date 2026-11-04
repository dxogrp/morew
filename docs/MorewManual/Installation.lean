import VersoManual

open Verso.Genre Manual

#doc (Manual) "Installation" =>
%%%
tag := "installation"
file := "installation"
htmlSplit := .never
%%%

Install [Lean through elan](https://lean-lang.org/install/).
Morew uses the Lean version in its `lean-toolchain` file, currently 4.33.0.

# Use Morew in a project

Use the same toolchain and add this dependency to your `lakefile.toml`:

```
[[require]]
name = "morew"
git = "https://github.com/dxogrp/morew.git"
rev = "main"
```

Run `lake update`, then `lake exe cache get` to download compiled Mathlib files.

# Build the repository

```
git clone https://github.com/dxogrp/morew.git
cd morew
lake exe cache get
lake build --wfail
```

# Imports

Use `import Morew` for the complete package. The mathematical modules
`Morew.Core`, `Morew.Transform`, `Morew.Conic`, `Morew.NLP`, and `Morew.Fn`
provide problems and equivalence, transformations, target forms, and modeling
functions. They make definitions and proofs available without installing
modeling commands or automatic rule registrations. Selective imports reduce
the dependencies that can trigger a rebuild.

For modeling commands, use `Morew.Reformulation.Basic`. Add
`Morew.Reformulation.Conic` or `Morew.Reformulation.NLP` for the corresponding
target commands and default automatic rules; each includes Basic. Import both
to use both target forms. Custom conic and NLP rules enter automatic selection through
`@[morew_conic]` or `@[morew_nlp]`; `using` selects a rule directly.
