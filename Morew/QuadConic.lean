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
`QuadConic.Form p` certifies equality with `p` on the same decision space;
a reformulation's `GlobalEquiv` certificate relates its source and target problems.

Import `Morew.Reformulation.Conic` for the `conic` and `qconic` commands.
-/
