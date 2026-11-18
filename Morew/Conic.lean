/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Conic.Basic
public import Morew.Conic.Exponential
public import Morew.Conic.PSD
public import Morew.Conic.PSD.LambdaMax
public import Morew.Conic.PSD.MatrixFraction
public import Morew.Conic.PSD.NuclearNorm
public import Morew.Conic.PSD.PosDef
public import Morew.Conic.PSD.SpectralNorm
public import Morew.Conic.Power
public import Morew.Conic.SecondOrder
public import Morew.Conic.SecondOrder.QuadForm

/-!
# Conic forms

Affine cone programs and representations using polyhedral, second-order,
exponential, power, and positive-semidefinite cones. Matrix representations
include quadratic-form epigraphs, Schur complements, spectral and nuclear norms,
matrix fractions, and positive-definite domains.

Import `Morew.Reformulation.Conic` for modeling commands and registered rules.
-/
