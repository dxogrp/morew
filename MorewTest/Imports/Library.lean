/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

namespace MorewTest.Imports.Library
open Morew

/-! Constructors remain usable from ordinary compiled definitions. -/

private def affineBasics :=
  (@Affine.Certified.const, @Affine.Certified.id, @Affine.Certified.transport)

private def affineArithmetic :=
  (@Affine.Certified.add, @Affine.Certified.sub, @Affine.Certified.neg,
    @Affine.Certified.realSMul, @Affine.Certified.natSMul, @Affine.Certified.smulConst,
    @Affine.Certified.mulConstLeft, @Affine.Certified.mulConstRight)

private def affinePowers :=
  (@Affine.Certified.powZero, @Affine.Certified.powZeroSource, @Affine.Certified.powOne,
    @Affine.Certified.rpowZeroSource, @Affine.Certified.rpowOne,
    @Affine.Certified.rpowNotationZeroSource, @Affine.Certified.rpowNotationOne)

private def affineCoordinates :=
  (@Affine.Certified.pair, @Affine.Certified.fst, @Affine.Certified.snd,
    @Affine.Certified.eval, @Affine.Certified.pi, @Affine.Certified.vecCons,
    @Affine.Certified.vecEmpty, @Affine.Certified.toEuclidean, @Affine.Certified.ofEuclidean)

private def affineSums :=
  (@Affine.Certified.sum, @Affine.Certified.dotConstLeft, @Affine.Certified.dotConstRight,
    @Affine.Certified.mulVec, @Affine.Certified.vecMul)

private def affineMatrices :=
  (@Affine.Certified.matrixOf, @Affine.Certified.transpose, @Affine.Certified.diagonal,
    @Affine.Certified.trace, @Affine.Certified.lowerTriangularMatrix,
    @Affine.Certified.submatrix, @Affine.Certified.reindex, @Affine.Certified.fromBlocks,
    @Affine.Certified.matrixMulConstLeft, @Affine.Certified.matrixMulConstRight)

private def affineSymmetricMatrices :=
  (@Affine.restrictSymmetricMatrix, @Affine.Certified.toSymmetricMatrix,
    @Affine.Certified.fromSymmetricMatrix, @Affine.Certified.fromBlocksFin)

private def coordinateSubstitutions :=
  (@Substitution.neg, @Substitution.addRight, @Substitution.addLeft,
    @Substitution.subRight, @Substitution.subLeft)

private def infinityNorm := @Fn.normInf

private def affineSpaces :=
  (@Elab.Affine.Space.Structure.real, @Elab.Affine.Space.Structure.euclidean,
    @Elab.Affine.Space.Structure.symmetricMatrix, @Elab.Affine.Space.Structure.prod,
    @Elab.Affine.Space.Structure.pi)

private def conicDomains :=
  (@Elab.Conic.Space.Domain.real, @Elab.Conic.Space.Domain.euclidean,
    @Elab.Conic.Space.Domain.symmetricMatrix, @Elab.Conic.Space.Domain.prod,
    @Elab.Conic.Space.Domain.pi)

private def polyhedralRepresentations :=
  (@Rewrite.absEpigraph, @Rewrite.posEpigraph, @Rewrite.maxEpigraph,
    @Rewrite.minHypograph, @Rewrite.finsetSupEpigraph, @Rewrite.finsetInfHypograph,
    @Rewrite.norm1Epigraph, @Rewrite.normInfEpigraph, @Rewrite.normInfToLpEpigraph,
    @Rewrite.fnNorm1Epigraph, @Rewrite.fnNormInfEpigraph)

private def euclideanRepresentations :=
  (@Rewrite.norm2Epigraph, @Rewrite.fnNorm2Epigraph)

private def secondOrderRepresentations :=
  (@Conic.SecondOrder.normEpigraph, @Conic.SecondOrder.fnNorm2Epigraph,
    @Conic.SecondOrder.normSquareEpigraph, @Conic.SecondOrder.fnNorm2SquareEpigraph,
    @Conic.SecondOrder.sumSquaresEpigraph, @Conic.SecondOrder.squareEpigraph,
    @Conic.SecondOrder.normSquareDivEpigraph, @Conic.SecondOrder.sumSquaresDivEpigraph,
    @Conic.SecondOrder.squareDivEpigraph)

private def exponentialRepresentations :=
  (@Conic.Exponential.expEpigraph, @Conic.Exponential.logHypograph,
    @Conic.Exponential.logSumExpEpigraph, @Conic.Exponential.logSumExpNativeEpigraph,
    @Conic.Exponential.softplusEpigraph, @Conic.Exponential.softplusNativeEpigraph,
    @Conic.Exponential.relEntrEpigraph, @Conic.Exponential.relEntrNativeEpigraph)

private def semidefiniteRepresentations :=
  (@Conic.posDefRepr, @Conic.MatrixFraction.epigraph, @Conic.MatrixFraction.nativeEpigraph,
    @Conic.Spectral.lambdaMaxEpigraph, @Conic.Spectral.spectralNormEpigraph,
    @Conic.Spectral.normNucEpigraph, @Conic.LogDet.hypograph, @Conic.LogDet.nativeHypograph)

private def powerRepresentations :=
  (@Conic.Power.rpowEpigraph, @Conic.Power.rpowNotationEpigraph,
    @Conic.Power.rpowNegativeEpigraph, @Conic.Power.rpowNegativeNotationEpigraph,
    @Conic.Power.rpowHypograph, @Conic.Power.rpowNotationHypograph,
    @Conic.Power.weightedGeoMeanHypograph, @Conic.Power.weightedGeoMeanNotationHypograph,
    @Conic.Power.weightedGeoMeanLeftNotationHypograph,
    @Conic.Power.weightedGeoMeanRightNotationHypograph)

private def constantAndLinearPowerRepresentations :=
  (@Conic.Power.rpowZeroEpigraph, @Conic.Power.rpowZeroHypograph,
    @Conic.Power.rpowOneEpigraph, @Conic.Power.rpowOneHypograph,
    @Conic.Power.rpowZeroNotationEpigraph, @Conic.Power.rpowZeroNotationHypograph,
    @Conic.Power.rpowOneNotationEpigraph, @Conic.Power.rpowOneNotationHypograph)

private def aggregatePowerRepresentations :=
  (@Conic.Power.geoMeanHypograph, @Conic.Power.invProdEpigraph, @Conic.Power.normEpigraph)

noncomputable section

def source := problem (x : ℝ) minimize x subject to
    first : |x| ≤ 2
    second : |x| ≤ 3
reformulation targeted : source := by
  conic at first
  nlp at second
reformulation asConic : targeted := by conic
reformulation asNLP : targeted := by nlp
example : IsConic asConic := asConic.isConic
example : IsSmoothNLP asNLP := asNLP.isSmoothNLP
example : GlobalEquiv source asConic := targeted.equiv.trans asConic.equiv
example : GlobalEquiv source asNLP := targeted.equiv.trans asNLP.equiv
end
end MorewTest.Imports.Library
