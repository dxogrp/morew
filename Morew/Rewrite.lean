/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Basic
import Morew.Rewrite.Polyhedral
import Morew.Rewrite.Euclidean

/-!
# Exact constraint rewrite representations

This semantic entry point provides the representation records and exact native
rules shared by constraint-rewriting commands. Import it to construct custom
`ExactConstraintLift`, `GraphRepresentation`, `EpigraphRepresentation`, or
`HypographRepresentation` evidence without loading the modeling language or
cone-specific semantics.
-/
