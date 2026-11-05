/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Polyhedral
import Morew.Conic.SecondOrder.Repr
import Morew.Conic.Exponential.Repr
import Morew.Conic.Power.Repr
import Morew.Conic.Power.Norm
import Morew.Conic.Power.GeometricMean
import Morew.Conic.PSD.Repr
import Morew.Elab.Rewrite.Registry

/-! Install built-in conic rules via `morew_conic`. Local attribute removal excludes a rule.
Automatic selection prefers `SecondOrder.normEpigraph` over `Power.normEpigraph`
when both certify; explicit selection bypasses this preference. -/

attribute [morew_conic]
  Morew.Conic.posDefRepr
  Morew.Conic.MatrixFraction.epigraph
  Morew.Conic.MatrixFraction.nativeEpigraph
  Morew.Conic.Spectral.lambdaMaxEpigraph
  Morew.Conic.Spectral.spectralNormEpigraph
  Morew.Conic.Spectral.normNucEpigraph
  Morew.Conic.LogDet.hypograph
  Morew.Conic.LogDet.nativeHypograph
  Morew.Rewrite.absEpigraph
  Morew.Rewrite.posEpigraph
  Morew.Rewrite.maxEpigraph
  Morew.Rewrite.minHypograph
  Morew.Rewrite.finsetSupEpigraph
  Morew.Rewrite.finsetInfHypograph
  Morew.Rewrite.norm1Epigraph
  Morew.Rewrite.normInfEpigraph
  Morew.Rewrite.normInfToLpEpigraph
  Morew.Rewrite.fnNorm1Epigraph
  Morew.Rewrite.fnNormInfEpigraph
  Morew.Conic.SecondOrder.normEpigraph
  Morew.Conic.SecondOrder.fnNorm2Epigraph
  Morew.Conic.SecondOrder.normSquareEpigraph
  Morew.Conic.SecondOrder.sumSquaresEpigraph
  Morew.Conic.SecondOrder.squareEpigraph
  Morew.Conic.SecondOrder.normSquareDivEpigraph
  Morew.Conic.SecondOrder.sumSquaresDivEpigraph
  Morew.Conic.SecondOrder.squareDivEpigraph
  Morew.Conic.Exponential.expEpigraph
  Morew.Conic.Exponential.logHypograph
  Morew.Conic.Exponential.logSumExpEpigraph
  Morew.Conic.Exponential.logSumExpNativeEpigraph
  Morew.Conic.Exponential.softplusEpigraph
  Morew.Conic.Exponential.softplusNativeEpigraph
  Morew.Conic.Exponential.relEntrEpigraph
  Morew.Conic.Exponential.relEntrNativeEpigraph
  Morew.Conic.Power.normEpigraph
  Morew.Conic.Power.geoMeanHypograph
  Morew.Conic.Power.invProdEpigraph
  Morew.Conic.Power.rpowEpigraph
  Morew.Conic.Power.rpowNotationEpigraph
  Morew.Conic.Power.rpowNegativeEpigraph
  Morew.Conic.Power.rpowNegativeNotationEpigraph
  Morew.Conic.Power.rpowHypograph
  Morew.Conic.Power.rpowNotationHypograph
  Morew.Conic.Power.weightedGeoMeanHypograph
  Morew.Conic.Power.weightedGeoMeanNotationHypograph
  Morew.Conic.Power.weightedGeoMeanLeftNotationHypograph
  Morew.Conic.Power.weightedGeoMeanRightNotationHypograph
  Morew.Conic.Power.rpowZeroEpigraph
  Morew.Conic.Power.rpowZeroHypograph
  Morew.Conic.Power.rpowOneEpigraph
  Morew.Conic.Power.rpowOneHypograph
  Morew.Conic.Power.rpowZeroNotationEpigraph
  Morew.Conic.Power.rpowZeroNotationHypograph
  Morew.Conic.Power.rpowOneNotationEpigraph
  Morew.Conic.Power.rpowOneNotationHypograph
