import VersoManual

open Verso.Genre Manual

#doc (Manual) "Installation" =>
%%%
tag := "installation"
file := "installation"
htmlSplit := .never
%%%

Install [Lean through elan](https://lean-lang.org/install/).

# Use Morew in a project

Choose a tag from [Releases](https://github.com/dxogrp/morew/releases)
and copy the `lean-toolchain` file from that tag into your project.

Add Morew to your `lakefile.toml`, replacing `<release-tag>` with the chosen tag:

```
[[require]]
name = "morew"
git = "https://github.com/dxogrp/morew.git"
rev = "<release-tag>"
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

For `conic`, `qconic`, and `conic at`, including basic modeling commands and
default rules:

```imports
import Morew.Reformulation.Conic
```

For NLP commands and default rules, including basic modeling commands:

```imports
import Morew.Reformulation.NLP
```

Import both command modules to use conic and NLP reformulations,
or import `Morew.Reformulation` for all reformulation commands.

For predefined atomic functions:

```imports
import Morew.Fn
```

For mathematical definitions and proofs:

```imports
import Morew.Core
import Morew.Transform
import Morew.Conic
import Morew.QuadConic
import Morew.NLP
```

These cover problems and equivalence, transformations, and target forms.

Register custom rules for automatic selection with `@[morew_conic]` or
`@[morew_nlp]`; see {ref "custom-rules"}[Custom rules].
