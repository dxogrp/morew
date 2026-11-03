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

Use `import Morew` for the complete package. The smaller command entry points are
`Morew.Reformulation.Basic`, `Morew.Reformulation.Conic`, and
`Morew.Reformulation.NLP`. Import both Conic and NLP to use both target forms.
