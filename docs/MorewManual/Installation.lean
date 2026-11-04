import VersoManual

open Verso.Genre Manual

#doc (Manual) "Installation" =>
%%%
tag := "installation"
file := "installation"
htmlSplit := .never
%%%

You need to install [Lean through elan](https://lean-lang.org/install/) to build Morew.
The Lean version used by Morew is specified in the `lean-toolchain` file.

# Use Morew in a project

Use the same toolchain and add this dependency to your `lakefile.toml`:

```
[[require]]
name = "morew"
git = "https://github.com/dxogrp/morew.git"
rev = "main"
```

Then run `lake update` to update the dependency.

# Build the repository

With Make installed, run:

```
git clone https://github.com/dxogrp/morew.git
cd morew
make cache  # Download precompiled Mathlib files.
make build  # Build the library, tests, and examples.
```

Run `make help` to see all available commands.

# Imports

To import the whole Morew package, use

```imports
import Morew
```

For basic modeling commands, use

```imports
import Morew.Reformulation.Basic
```

For conic target commands and default automatic rules, use

```imports
import Morew.Reformulation.Conic
```

which includes Basic.

For NLP target commands and default automatic rules, use

```imports
import Morew.Reformulation.NLP
```

which includes Basic.
Import both target modules to use both target forms.

To use predefined atomic functions, use

```imports
import Morew.Fn
```

For mathematical definitions and proofs, use

```imports
import Morew.Core
import Morew.Transform
import Morew.Conic
import Morew.NLP
```

These cover problems and equivalence, transformations, and target forms.

Custom conic and NLP rules can be registered for automatic selection by tagging them with

```
@[morew_conic]
```

or

```
@[morew_nlp]
```
