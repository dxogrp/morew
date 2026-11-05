/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic
import MorewTest.Reformulation.Spectral.Defined
import MorewTest.Reformulation.PrintSupport

/-! Exact spectral rows use the source norm and preserve rectangular dimensions. -/

namespace MorewTest.Reformulation.Spectral

open Morew Morew.Conic

noncomputable section

def largestSource (n : Nat) :=
  problem (A : SymmetricMatrix n) (t : ℝ)
    minimize t
    subject to
      bound : Fn.lambdaMax A.toMatrix ≤ t

variable (n : Nat) (hn : 0 < n)

reformulation largestTarget : (largestSource n) := by conic
example : GlobalEquiv (largestSource n) (largestTarget n) :=
  largestTarget.equiv n hn
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
example : GlobalEquiv (conjoinedLargestSource n P) (conjoinedLargest n P hP) :=
  conjoinedLargest.equiv n hn P hP
end Symmetric

section PosDef
variable (hP : P.PosDef ∧ True)
reformulation conjoinedPositiveLargest : (conjoinedLargestSource n P) := by conic
example : GlobalEquiv (conjoinedLargestSource n P)
    (conjoinedPositiveLargest n P hP) :=
  conjoinedPositiveLargest.equiv n hn P hP
end PosDef

section Universal
variable (family : Fin 2 → Matrix (Fin n) (Fin n) ℝ)
  (hFamily : ∀ i, True ∧ (family i).IsSymm)
reformulation conjoinedUniversalLargest : (conjoinedLargestSource n (family 0)) := by conic
example : GlobalEquiv (conjoinedLargestSource n (family 0))
    (conjoinedUniversalLargest n family hFamily) :=
  conjoinedUniversalLargest.equiv n hn family hFamily
end Universal

end ConjoinedSymmetry

variable (m : Nat)

example : GlobalEquiv (normSource m n) (normTarget (m := m) (n := n)) :=
  normTarget.equiv (m := m) (n := n)
example : (normTarget.conicForm (m := m) (n := n)).data.rowCount = 2 := rfl
example : IsConic (normTarget (m := m) (n := n)) :=
  normTarget.isConic (m := m) (n := n)
example : (normTarget.conicForm (m := m) (n := n)).data.toProblem =
    normTarget (m := m) (n := n) :=
  (normTarget.conicForm (m := m) (n := n)).represents

reformulation normObjectiveTarget : normObjective := by
  epigraph t
  conic

example : GlobalEquiv normObjective normObjectiveTarget := normObjectiveTarget.equiv
example : IsConic normObjectiveTarget := normObjectiveTarget.isConic

example : GlobalEquiv (nuclearSource m n) (nuclearTarget (m := m) (n := n)) :=
  nuclearTarget.equiv (m := m) (n := n)
example : (nuclearTarget.conicForm (m := m) (n := n)).data.rowCount = 2 := rfl
example : IsConic (nuclearTarget (m := m) (n := n)) :=
  nuclearTarget.isConic (m := m) (n := n)

reformulation nuclearChained : (nuclearIntermediate (m := m) (n := n)) := by conic
example : GlobalEquiv (nuclearSource m n) (nuclearChained (m := m) (n := n)) :=
  (nuclearIntermediate.equiv (m := m) (n := n)).trans
    (nuclearChained.equiv (m := m) (n := n))

def nuclearObjective :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ)
    minimize Fn.normNuc A
    subject to
      anchor : A 0 0 = 1

reformulation nuclearObjectiveTarget : nuclearObjective := by
  epigraph t
  conic

def nuclearCollision :=
  problem (A : Matrix (Fin 2) (Fin 3) ℝ) (bound_aux t : ℝ)
    maximize bound_aux
    subject to
      bound : Fn.normNuc A ≤ t

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
example : IsConic emptyNorm := emptyNorm.isConic
example : IsConic emptyNuclear := emptyNuclear.isConic

open scoped Matrix.Norms.L2Operator in
def affineSource (m n : Nat) (B : Matrix (Fin m) (Fin n) ℝ) :=
  problem (A : Matrix (Fin m) (Fin n) ℝ) (t : ℝ)
    minimize t
    subject to
      operator : ‖(2 : ℝ) • A + B‖ ≤ t + 1
      nuclear : Fn.normNuc A.transpose ≤ t

variable (B : Matrix (Fin m) (Fin n) ℝ)

reformulation affineTarget : (affineSource m n B) := by conic
example : GlobalEquiv (affineSource m n B) (affineTarget (m := m) (n := n) B) :=
  affineTarget.equiv (m := m) (n := n) B
example : (affineTarget.conicForm (m := m) (n := n) B).data.rowCount = 4 := rfl

end
end MorewTest.Reformulation.Spectral
