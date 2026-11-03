/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Basic

/-!
# Exact real power cones

`POW α` is the set of triples `(x, y, z)` satisfying `0 ≤ x`, `0 ≤ y`, and
`|z| ≤ x ^ α * y ^ (1 - α)`. The set is defined for all real `α`; the bundled
`Cone.power α hα` uses a proof of `0 < α ∧ α < 1`.

This module provides the cone and scalar power identities.
`Morew.Conic.Power.Representations` supplies the corresponding rewrite records,
`Morew.Conic.Power.Norm` treats finite p-norms, and
`Morew.Conic.Power.GeometricMean` treats geometric means and inverse products.
All parameters are exact real values, and each representation states its
domain and dimension assumptions.
-/
