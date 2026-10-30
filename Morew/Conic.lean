/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Basic
import Morew.Conic.Exponential
import Morew.Conic.Polyhedral
import Morew.Conic.PSD
import Morew.Conic.Power
import Morew.Conic.SecondOrder

/-!
# Certified conic forms

Public entry point for the semantic affine cone-program API, its base cones,
and checked representation, convexity, and exact polyhedral, second-order,
exponential, real-power, and positive-semidefinite bounds, including exact Schur
complement identities. This import does not install the problem or
reformulation DSL.
-/
