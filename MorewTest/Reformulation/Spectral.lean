/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Reformulation.PrintDetails

/-! Exact spectral rows use the source norm and preserve rectangular dimensions. -/

namespace MorewTest.Reformulation.Spectral

open Morew Morew.Conic
open scoped Matrix.Norms.L2Operator

noncomputable section

def largestSource (n : Nat) :=
  problem (A : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      bound : Fn.lambdaMax A.toMatrix ≤ t

variable (n : Nat) (hn : 0 < n)

reformulation largestTarget : (largestSource n) := by conic
example : GlobalEquivalence (largestSource n) (largestTarget n) :=
  largestTarget.equivalence n hn
example : (largestTarget.conicForm n).data.rowCount = 1 := rfl

def conjoinedLargestSource (n : Nat) (P : Matrix (Fin n) (Fin n) ℝ) :=
  problem (a t : ℝ)
    minimize t
    subject to bound : Fn.lambdaMax (a • 1 + P) ≤ t

section ConjoinedSymmetry

variable (P : Matrix (Fin n) (Fin n) ℝ)

section Symmetric
variable (hP : True ∧ (P.IsSymm ∧ True))
reformulation conjoinedLargest : (conjoinedLargestSource n P) := by conic
example : GlobalEquivalence (conjoinedLargestSource n P) (conjoinedLargest n P hP) :=
  conjoinedLargest.equivalence n hn P hP
end Symmetric

section PositiveDefinite
variable (hP : P.PosDef ∧ True)
reformulation conjoinedPositiveLargest : (conjoinedLargestSource n P) := by conic
example : GlobalEquivalence (conjoinedLargestSource n P)
    (conjoinedPositiveLargest n P hP) :=
  conjoinedPositiveLargest.equivalence n hn P hP
end PositiveDefinite

section Universal
variable (family : Fin 2 → Matrix (Fin n) (Fin n) ℝ)
  (hFamily : ∀ i, True ∧ (family i).IsSymm)
reformulation conjoinedUniversalLargest : (conjoinedLargestSource n (family 0)) := by conic
example : GlobalEquivalence (conjoinedLargestSource n (family 0))
    (conjoinedUniversalLargest n family hFamily) :=
  conjoinedUniversalLargest.equivalence n hn family hFamily
end Universal

end ConjoinedSymmetry

def normSource (m n : Nat) :=
  problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖A‖ ≤ t

variable (m : Nat)

reformulation normTarget : (normSource m n) := by conic
example : GlobalEquivalence (normSource m n) (normTarget (m := m) (n := n)) :=
  normTarget.equivalence (m := m) (n := n)
example : (normTarget.conicForm (m := m) (n := n)).data.rowCount = 2 := rfl

def normObjective :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize ‖A‖
    subject to
      anchor : A 0 0 = 1

reformulation normObjectiveTarget : normObjective := by
  epigraph t
  conic

example : GlobalEquivalence normObjective normObjectiveTarget := normObjectiveTarget.equivalence

def nuclearSource (m n : Nat) :=
  problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    minimize t
    subject to
      bound : Fn.nuclearNorm A ≤ t

reformulation nuclearTarget : (nuclearSource m n) := by conic
example : GlobalEquivalence (nuclearSource m n) (nuclearTarget (m := m) (n := n)) :=
  nuclearTarget.equivalence (m := m) (n := n)
example : (nuclearTarget.conicForm (m := m) (n := n)).data.rowCount = 2 := rfl

reformulation nuclearIntermediate : (nuclearSource m n) := by conic at bound
reformulation nuclearChained : (nuclearIntermediate (m := m) (n := n)) := by conic
example : GlobalEquivalence (nuclearSource m n) (nuclearChained (m := m) (n := n)) :=
  (nuclearIntermediate.equivalence (m := m) (n := n)).trans
    (nuclearChained.equivalence (m := m) (n := n))

def nuclearObjective :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize Fn.nuclearNorm A
    subject to
      anchor : A 0 0 = 1

reformulation nuclearObjectiveTarget : nuclearObjective := by
  epigraph t
  conic

def nuclearCollision :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (bound_aux t : ℝ)
    maximize bound_aux
    subject to
      bound : Fn.nuclearNorm A ≤ t

reformulation nuclearCollisionTarget : nuclearCollision := by conic

run_cmd do
  let printed ← PrintDetails.printed ``nuclearCollisionTarget false
  unless printed.contains "bound_aux_1" && printed.contains "SymmetricMatrix 2 × SymmetricMatrix 3" &&
      printed.contains "PSD (2 + 3)" && printed.contains "/ 2" do
    Lean.throwError "nuclear auxiliaries, block dimension, or half trace changed: {printed}"
  let detailed ← PrintDetails.printed ``nuclearCollisionTarget true
  unless detailed.contains "/ 2" do Lean.throwError "detailed printing lost half-trace normalization"

reformulation emptyNorm : (normSource 0 0) := by conic
reformulation emptyNuclear : (nuclearSource 0 0) := by conic
example : emptyNorm.conicForm.data.rowCount = 2 := rfl
example : emptyNuclear.conicForm.data.rowCount = 2 := rfl

def affineSource (m n : Nat) (B : Matrix (Fin m) (Fin n) ℝ) :=
  problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    minimize t
    subject to
      operator : ‖(2 : ℝ) • A + B‖ ≤ t + 1
      nuclear : Fn.nuclearNorm A.transpose ≤ t

variable (B : Matrix (Fin m) (Fin n) ℝ)

reformulation affineTarget : (affineSource m n B) := by conic
example : GlobalEquivalence (affineSource m n B) (affineTarget (m := m) (n := n) B) :=
  affineTarget.equivalence (m := m) (n := n) B
example : (affineTarget.conicForm (m := m) (n := n) B).data.rowCount = 4 := rfl

end
end MorewTest.Reformulation.Spectral
