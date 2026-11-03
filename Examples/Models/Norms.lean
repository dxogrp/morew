/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import Morew.Reformulation.NLP

/-!
# Vector norm models

`Fn.norm1`, `Fn.norm2`, and `Fn.normInf` denote the sum of absolute coordinates,
Euclidean norm, and maximum absolute coordinate, respectively. They operate on
ordinary real vectors without requiring a norm scope or a `WithLp` conversion.
Native notation `‖WithLp.toLp p x‖` instead selects the `PiLp` p-norm; the
Euclidean and finite p-norm examples below use it to choose an exponent.

The models fit data under norm bounds, compare three exact Euclidean
representations at a symbolic dimension, and express a finite p-norm with
power cones. Each complete formulation has conic or smooth NLP certification.
-/

namespace Examples.Models.Norms

open Morew

noncomputable section

namespace NormBudget

def normBudget (b : Fin n → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm1 (x - b)
    subject to
      radius : Fn.norm2 x ≤ 2
      peak : Fn.normInf x ≤ 1

variable (b : Fin n → ℝ)

reformulation normConic : (normBudget b) := by
  epigraph t as residualBound
  conic at radius
  conic

#printp normConic

example : GlobalEquivalence (normBudget b) (normConic b) := normConic.equivalence b
example : (normConic.conicForm b).data.toProblem = normConic b :=
  (normConic.conicForm b).represents
example : IsConic (normConic b) := normConic.isConic b

-- The same source model can instead use the smooth polynomial representation.
reformulation normNLP : (normBudget b) := by
  epigraph t as residualBound
  nlp at radius
  nlp

#printp normNLP

example : GlobalEquivalence (normBudget b) (normNLP b) := normNLP.equivalence b
example : (normNLP.nlpForm b).data.toProblem = normNLP b :=
  (normNLP.nlpForm b).represents
example : IsSmoothNLP (normNLP b) := normNLP.isSmoothNLP b

end NormBudget

namespace Euclidean

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖WithLp.toLp 2 x‖ ≤ t

variable (n : ℕ)

-- Automatic conic rewriting uses one SOC constraint on (t, x).
reformulation soc : (source n) := by
  conic

#printp soc
example : GlobalEquivalence (source n) (soc n) := soc.equivalence n
example : Conic.Form (soc n) := soc.conicForm n
example : (soc.conicForm n).data.toProblem = soc n := (soc.conicForm n).represents
example : IsConic (soc n) := soc.isConic n

-- Selecting the power rule adds r, with 0 ≤ t, ∑ i, r i ≤ t, and
-- (r i, t, x i) ∈ POW (1/2) for each coordinate.
reformulation power : (source n) := by
  conic at bound using Morew.Conic.Power.normEpigraph
  conic

#printp power
example : GlobalEquivalence (source n) (power n) := power.equivalence n
example : Conic.Form (power n) := power.conicForm n
example : (power.conicForm n).data.toProblem = power n := (power.conicForm n).represents
example : IsConic (power n) := power.isConic n

-- Smooth NLP rewriting yields 0 ≤ t and ∑ i, x i ^ 2 ≤ t ^ 2,
-- preserving the symbolic dimension n.
reformulation squaredNorm : (source n) := by
  nlp

#printp squaredNorm
example : GlobalEquivalence (source n) (squaredNorm n) := squaredNorm.equivalence n
example : (squaredNorm.nlpForm n).data.toProblem = squaredNorm n :=
  (squaredNorm.nlpForm n).represents
example : IsSmoothNLP (squaredNorm n) := squaredNorm.isSmoothNLP n

end Euclidean

namespace PNorm

def source (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖WithLp.toLp (3 / 2) x‖ ≤ t

variable (n : ℕ)

reformulation ready : (source n) := by
  conic

-- The exact cone exponent is 2/3, with one auxiliary coordinate per input.
#printp ready
example : GlobalEquivalence (source n) (ready n) := ready.equivalence n
example : (ready.conicForm n).data.toProblem = ready n := (ready.conicForm n).represents
example : IsConic (ready n) := ready.isConic n

end PNorm

namespace NormBound

def p :=
  problem (x : Fin 2 → ℝ)
    minimize (x 0 - 1) ^ 2 + (x 1 + 2) ^ 2
    subject to
      radius : Fn.norm2 x ≤ 5

-- Bound each square separately so the final objective is affine.
reformulation coneBound : p := by
  conic at radius
  epigraph a at ((x 0 - 1) ^ 2) as firstSquare
  epigraph b at ((x 1 + 2) ^ 2) as secondSquare
  conic

#printp coneBound
example : GlobalEquivalence p coneBound := coneBound.equivalence
example : IsConic coneBound := coneBound.isConic

end NormBound

end
end Examples.Models.Norms
