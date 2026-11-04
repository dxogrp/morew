import VersoManual

open Verso.Genre Manual

#doc (Manual) "Installation" =>
%%%
tag := "installation"
file := "installation"
htmlSplit := .never
%%%

Install [Lean through elan](https://lean-lang.org/install/).
Morew's Lean version is specified in `lean-toolchain`.

# Use Morew in a project

Use the same toolchain and add this dependency to your `lakefile.toml`:

```
[[require]]
name = "morew"
git = "https://github.com/dxogrp/morew.git"
rev = "main"
```

Then run `lake update`.

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

To import the whole package:

```imports
import Morew
```

For basic modeling commands:

```imports
import Morew.Reformulation.Basic
```

For conic commands and default rules, including basic modeling commands:

```imports
import Morew.Reformulation.Conic
```

For NLP commands and default rules, including basic modeling commands:

```imports
import Morew.Reformulation.NLP
```

Import both target modules to use both target forms.

For predefined atomic functions:

```imports
import Morew.Fn
```

For mathematical definitions and proofs:

```imports
import Morew.Core
import Morew.Transform
import Morew.Conic
import Morew.NLP
```

These cover problems and equivalence, transformations, and target forms.

Register custom rules for automatic selection with `@[morew_conic]` or
`@[morew_nlp]`; see {ref "custom-rules"}[Custom rules].
