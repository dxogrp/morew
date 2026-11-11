/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Basic
import Morew.Conic.Exponential
import Morew.Conic.PSD
import Morew.Conic.PSD.LambdaMax
import Morew.Conic.PSD.MatrixFraction
import Morew.Conic.PSD.NuclearNorm
import Morew.Conic.PSD.PosDef
import Morew.Conic.PSD.SpectralNorm
import Morew.Conic.Power
import Morew.Conic.SecondOrder

/-!
# Conic forms

Affine cone programs and representations using polyhedral, second-order,
exponential, power, and positive-semidefinite cones. Matrix representations
include Schur complements, spectral and nuclear norms, matrix fractions, and
positive-definite domains.

Import `Morew.Reformulation.Conic` for modeling commands and registered rules.
-/
