/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.LogDet.Sources

/-! Log-det rewriting uses domain conditions from grouped constraints, positive
margins, auxiliary matrices, and fixed or affine arguments. -/

namespace MorewTest.Reformulation.LogDet

open Morew Morew.Conic

noncomputable section

variable (n : Nat) (hn : 0 < n)

def groupedSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      group : (let matrix := X.toMatrix; matrix.PosDef ∧ t ≤ Fn.logDet matrix)
      another : 2 * t - 1 ≤ Fn.logDet X.toMatrix

reformulation groupedTarget : (groupedSource n) := by conic
example : (groupedTarget.conicForm n).data.rowCount = 7 := rfl
example : GlobalEquivalence (groupedSource n) (groupedTarget n) :=
  groupedTarget.equivalence n hn

def marginSource (n : Nat) (epsilon : ℝ) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      margin : (X.toMatrix - epsilon • 1).PosSemidef
      bound : t ≤ Fn.logDet X.toMatrix

variable (epsilon : ℝ) (hε : 0 < epsilon)

reformulation marginTarget : (marginSource n epsilon) := by conic
example : GlobalEquivalence (marginSource n epsilon) (marginTarget n epsilon) :=
  marginTarget.equivalence n hn epsilon hε

def bundledMarginSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      margin : X - (2 : ℝ) • SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one ∈ PSD n
      bound : t ≤ Fn.logDet X.toMatrix

reformulation bundledMarginTarget : (bundledMarginSource n) := by conic
example : GlobalEquivalence (bundledMarginSource n) (bundledMarginTarget n) :=
  bundledMarginTarget.equivalence n hn

def witnessedSource (n : Nat) :=
  problem (X W : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      witness : SymmetricMatrix.fromBlocks X 1 W ∈ PSD (n + n)
      bound : t ≤ Fn.logDet X.toMatrix

reformulation witnessedTarget : (witnessedSource n) := by conic
example : (witnessedTarget.conicForm n).data.rowCount = 4 := rfl

def nativeWitnessedSource (n : Nat) :=
  problem (X W : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      group : (let matrix := X.toMatrix;
        (fromBlocksFin matrix 1 1 W.toMatrix).PosSemidef ∧ t ≤ Fn.logDet matrix)

reformulation nativeWitnessedTarget : (nativeWitnessedSource n) := by conic
example : GlobalEquivalence (nativeWitnessedSource n) (nativeWitnessedTarget n) :=
  nativeWitnessedTarget.equivalence n hn

def fixedSource (n : Nat) (X : Matrix (Fin n) (Fin n) ℝ) :=
  problem (t : ℝ)
    maximize t
    subject to bound : t ≤ Fn.logDet X

variable (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.PosDef)

reformulation fixedTarget : (fixedSource n X) := by
  conic at bound
  conic
example : GlobalEquivalence (fixedSource n X) (fixedTarget n X hX) :=
  fixedTarget.equivalence n hn X hX
example : (fixedTarget.conicForm n X hX).data.rowCount = 3 := rfl

section ConjoinedDomain

variable (family : Fin 2 → Matrix (Fin n) (Fin n) ℝ)
  (hFamily : True ∧ (∀ i, (family i).PosDef ∧ True))

reformulation fixedConjoinedTarget : (fixedSource n (family 0)) := by
  conic at bound
  conic
example : GlobalEquivalence (fixedSource n (family 0))
    (fixedConjoinedTarget n family hFamily) :=
  fixedConjoinedTarget.equivalence n hn family hFamily

end ConjoinedDomain

def affineSource (n : Nat) :=
  problem (X : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to
      domain : ((2 : ℝ) • X.toMatrix + 1).PosDef
      bound : t + 1 ≤ Fn.logDet ((2 : ℝ) • X.toMatrix + 1)

reformulation affineTarget : (affineSource n) := by conic
example : GlobalEquivalence (affineSource n) (affineTarget n) :=
  affineTarget.equivalence n hn

end
end MorewTest.Reformulation.LogDet
