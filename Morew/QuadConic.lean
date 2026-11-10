/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.QuadConic.Basic
import Morew.QuadConic.Objective

/-!
# Quadratic conic forms

Represent objectives as a quadratic form plus an affine map, with affine cone
constraints and curvature evidence for the stored optimization direction.

Import `Morew.Reformulation.Conic` for the `conic` and `qconic` commands.
-/
