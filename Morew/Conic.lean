/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Basic
import Morew.Conic.Exponential
import Morew.Conic.Polyhedral
import Morew.Conic.PSD
import Morew.Conic.PSD.LambdaMax
import Morew.Conic.PSD.MatrixFraction
import Morew.Conic.PSD.NuclearNorm
import Morew.Conic.PSD.PositiveDefinite
import Morew.Conic.PSD.SpectralNorm
import Morew.Conic.Power
import Morew.Conic.SecondOrder

/-!
# Certified conic forms

Public entry point for the semantic affine cone-program API, its base cones,
and checked representation, convexity, and exact polyhedral, second-order,
exponential, real-power, and positive-semidefinite bounds, including exact Schur
complement, spectral, nuclear-norm, matrix-fraction, and positive-definite-domain
equivalences. Rewrite records are available from
`Morew.Conic.PSD.Representations`. This import does not install the problem or
reformulation DSL.
-/
