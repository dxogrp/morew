/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Power.Basic

/-!
# Exact real power cones

`POW α` is the set of triples `(x, y, z)` satisfying `0 ≤ x`, `0 ≤ y`, and
`|z| ≤ x ^ α * y ^ (1 - α)`. The bundled `Cone.power α hα` requires a checked
proof of `0 < α ∧ α < 1`; the set notation itself carries no range assumption.
Parameters are exact real values, including irrational values.

Scalar epigraphs with exponent greater than one require a nonnegative base;
negative exponents require a strictly positive base. Fractional-power and binary
weighted-geometric-mean hypographs introduce a nonnegative auxiliary above the
bound, so negative bounds remain valid. The semantic equivalences include zero
boundaries explicitly.

This narrow import provides the cone and its mathematical equivalences without
installing rewrite registrations or the modeling language. Representation records
are available from `Morew.Conic.Power.Representations`.

`Morew.Conic.Power.Norm` provides the native finite p-norm representation for
`1 < p.toReal`, including empty coordinate spaces. The nonempty geometric-mean
and inverse-product representations are in `Morew.Conic.Power.GeometricMean`;
their ordinary modeling functions are in `Morew.Fn.Power`. These finite lifts
use exact power parameters and deterministic auxiliary coordinate order.
-/
