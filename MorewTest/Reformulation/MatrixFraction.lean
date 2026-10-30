/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Reformulation.PrintDetails

/-! Matrix-fraction domains survive either targeted or terminal rewrite order. -/

namespace MorewTest.Reformulation.MatrixFraction

open Morew Morew.Conic
open scoped Matrix

noncomputable section

def source (n : Nat) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      domain : P.toMatrix.PosDef
      bound : Fn.matrixFrac x P.toMatrix ≤ t

variable (n : Nat)

reformulation terminal : (source n) := by conic

reformulation domainIntermediate : (source n) := by conic at domain

reformulation domainFirst : (source n) := by
  conic at domain
  conic at bound
  conic

reformulation fractionFirst : (source n) := by
  conic at bound
  conic at domain
  conic

example : GlobalEquivalence (source n) (terminal n) := terminal.equivalence n
example : IsConic (terminal n) := terminal.isConic n
example : (terminal.conicForm n).data.rowCount = 2 := rfl
example : GlobalEquivalence (source n) (domainFirst n) := domainFirst.equivalence n
example : GlobalEquivalence (source n) (fractionFirst n) := fractionFirst.equivalence n

def reverseSource (n : Nat) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      bound : x ⬝ᵥ (P.toMatrix⁻¹ *ᵥ x) ≤ t
      domain : P.toMatrix.PosDef

reformulation reverseTarget : (reverseSource n) := by conic

def groupedSource (n : Nat) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      group : (let pivot := P.toMatrix; pivot.PosDef ∧ Fn.matrixFrac x pivot ≤ t)
      another : Fn.matrixFrac (2 • x) P.toMatrix ≤ 2 * t

reformulation groupedTarget : (groupedSource n) := by conic
example : (groupedTarget.conicForm n).data.rowCount = 3 := rfl

def marginSource (n : Nat) (epsilon : ℝ) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      margin : (P.toMatrix - epsilon • 1).PosSemidef
      bound : Fn.matrixFrac x P.toMatrix ≤ t

variable (epsilon : ℝ) (h : 0 < epsilon)

reformulation marginTarget : (marginSource n epsilon) := by conic
example : GlobalEquivalence (marginSource n epsilon) (marginTarget n epsilon) :=
  marginTarget.equivalence n epsilon h

def fixedSource (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.matrixFrac x P ≤ t

variable (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)

reformulation fixedTarget : (fixedSource n P) := by conic
example : GlobalEquivalence (fixedSource n P) (fixedTarget n P hP) :=
  fixedTarget.equivalence n P hP

def witnessedSource (n : Nat) :=
  problem (x : Fin n → ℝ) (P W : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      witness : SymmetricMatrix.fromBlocks P 1 W ∈ PSD (n + n)
      bound : Fn.matrixFrac x P.toMatrix ≤ t

reformulation witnessedTarget : (witnessedSource n) := by conic
example : (witnessedTarget.conicForm n).data.rowCount = 2 := rfl

def bundledMarginSource (n : Nat) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      margin : P - (2 : ℝ) • SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one ∈ PSD n
      bound : Fn.matrixFrac x P.toMatrix ≤ t

reformulation bundledMarginTarget : (bundledMarginSource n) := by conic
example : GlobalEquivalence (bundledMarginSource n) (bundledMarginTarget n) :=
  bundledMarginTarget.equivalence n

end
end MorewTest.Reformulation.MatrixFraction
