/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.MatrixFraction.Defined

/-! Matrix-fraction domains survive either targeted or terminal rewrite order. -/

namespace MorewTest.Reformulation.MatrixFraction

open Morew Morew.Conic
open scoped Matrix

noncomputable section

variable (n : Nat)

reformulation terminal : (source n) := by conic

reformulation domainFirst : (source n) := by
  conic at domain
  conic at bound
  conic

reformulation fractionFirst : (source n) := by
  conic at bound
  conic at domain
  conic

example : GlobalEquiv (source n) (terminal n) := terminal.equiv n
example : IsConic (terminal n) := terminal.isConic n
example : (terminal.conicForm n).data.rowCount = 2 := rfl
example : GlobalEquiv (source n) (domainFirst n) := domainFirst.equiv n
example : GlobalEquiv (source n) (fractionFirst n) := fractionFirst.equiv n

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
      group : (let pivot := P.toMatrix; pivot.PosDef ∧ Fn.matFrac x pivot ≤ t)
      another : Fn.matFrac (2 • x) P.toMatrix ≤ 2 * t

reformulation groupedTarget : (groupedSource n) := by conic
example : (groupedTarget.conicForm n).data.rowCount = 3 := rfl

def marginSource (n : Nat) (epsilon : ℝ) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      margin : (P.toMatrix - epsilon • 1).PosSemidef
      bound : Fn.matFrac x P.toMatrix ≤ t

variable (epsilon : ℝ) (h : 0 < epsilon)

reformulation marginTarget : (marginSource n epsilon) := by conic
example : GlobalEquiv (marginSource n epsilon) (marginTarget n epsilon) :=
  marginTarget.equiv n epsilon h

def fixedSource (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to bound : Fn.matFrac x P ≤ t

-- Independent domain evidence also certifies the global symmetry of the
-- resulting Schur block, including conjunctions beneath universal binders.
section ConjoinedDomains

variable (Q : Matrix (Fin n) (Fin n) ℝ)

section Nested
variable (hQ : True ∧ (Q.PosDef ∧ True))
reformulation fixedConjoinedNested : (fixedSource n Q) := by conic
example : GlobalEquiv (fixedSource n Q) (fixedConjoinedNested n Q hQ) :=
  fixedConjoinedNested.equiv n Q hQ
end Nested

section Universal
variable (family : Fin 2 → Matrix (Fin n) (Fin n) ℝ)
  (hFamily : ∀ i, True ∧ ((family i).PosDef ∧ True))
reformulation fixedConjoinedUniversal : (fixedSource n (family 0)) := by conic
example : GlobalEquiv (fixedSource n (family 0))
    (fixedConjoinedUniversal n family hFamily) :=
  fixedConjoinedUniversal.equiv n family hFamily
end Universal

section OuterConjunction
variable (family : Fin 2 → Matrix (Fin n) (Fin n) ℝ)
  (hFamily : True ∧ (∀ i, (family i).PosDef ∧ True))
reformulation fixedConjoinedOuterUniversal : (fixedSource n (family 0)) := by conic
example : GlobalEquiv (fixedSource n (family 0))
    (fixedConjoinedOuterUniversal n family hFamily) :=
  fixedConjoinedOuterUniversal.equiv n family hFamily
end OuterConjunction

end ConjoinedDomains

variable (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)

reformulation fixedTarget : (fixedSource n P) := by conic
example : GlobalEquiv (fixedSource n P) (fixedTarget n P hP) :=
  fixedTarget.equiv n P hP

def witnessedSource (n : Nat) :=
  problem (x : Fin n → ℝ) (P W : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      witness : SymmetricMatrix.fromBlocks P 1 W ∈ PSD (n + n)
      bound : Fn.matFrac x P.toMatrix ≤ t

reformulation witnessedTarget : (witnessedSource n) := by conic
example : (witnessedTarget.conicForm n).data.rowCount = 2 := rfl

def bundledMarginSource (n : Nat) :=
  problem (x : Fin n → ℝ) (P : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      margin : P - (2 : ℝ) • SymmetricMatrix.ofMatrix 1 Matrix.isSymm_one ∈ PSD n
      bound : Fn.matFrac x P.toMatrix ≤ t

reformulation bundledMarginTarget : (bundledMarginSource n) := by conic
example : GlobalEquiv (bundledMarginSource n) (bundledMarginTarget n) :=
  bundledMarginTarget.equiv n

end
end MorewTest.Reformulation.MatrixFraction
