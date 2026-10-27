/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite.Polyhedral
import Morew.Conic.SecondOrder.Representations
import Morew.Conic.Exponential.Representations
import Morew.Elab.Rewrite.Registry

/-!
# Registered built-in conic rules

Built-in records use the same public attribute as downstream extensions. Import
this module to make these rules available; ordinary local attribute removal can
exclude an individual rule from automatic discovery.
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
