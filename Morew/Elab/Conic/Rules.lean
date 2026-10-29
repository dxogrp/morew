/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Polyhedral
import Morew.Conic.SecondOrder.Representations
import Morew.Conic.Exponential.Representations
import Morew.Conic.Power.Representations
import Morew.Conic.Power.Norm
import Morew.Conic.Power.GeometricMean
import Morew.Elab.Rewrite.Registry

/-!
# Registered built-in conic rules

Built-in records use the same public attribute as downstream extensions. Import
this module to make these rules available; ordinary local attribute removal can
exclude an individual rule from automatic discovery.

The conic consumer prefers `SecondOrder.normEpigraph` over `Power.normEpigraph`
when both fully certify the selected constraint. Other successful rules retain
their ambiguity, and explicit `using` selection bypasses this preference.
-/

attribute [morew_conic]
  Morew.Rewrite.absEpigraph
  Morew.Rewrite.posEpigraph
  Morew.Rewrite.maxEpigraph
  Morew.Rewrite.minHypograph
  Morew.Rewrite.finsetSupEpigraph
  Morew.Rewrite.finsetInfHypograph
  Morew.Rewrite.norm1Epigraph
  Morew.Rewrite.normInfEpigraph
  Morew.Rewrite.normInfToLpEpigraph
  Morew.Conic.SecondOrder.normEpigraph
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
  Morew.Conic.Exponential.relativeEntropyEpigraph
  Morew.Conic.Exponential.relativeEntropyNativeEpigraph
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
