/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic
public import MorewTest.ElabSupport
public import MorewTest.Reformulation.Spectral.Defined
public import MorewTest.Reformulation.PrintSupport

/-! Exact spectral rows preserve eigenvalue bounds, source norms, and matrix dimensions. -/

@[expose] public section

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

def smallestSource (n : Nat) :=
  problem (A : SymmetricMatrix n) (t : ℝ)
    maximize t
    subject to bound : t ≤ Fn.lambdaMin A.toMatrix

reformulation smallestTarget : (smallestSource n) := by conic

reformulation smallestExplicit : (smallestSource n) := by
  conic at bound using Spectral.lambdaMinHypograph
  conic

reformulation smallestCertificate : (smallestSource n) := by
  conic at bound using (Spectral.lambdaMinHypograph hn)
  conic

example : GlobalEquiv (smallestSource n) (smallestTarget n) :=
  smallestTarget.equiv n hn
example : GlobalEquiv (smallestSource n) (smallestExplicit n) :=
  smallestExplicit.equiv n hn
example : GlobalEquiv (smallestSource n) (smallestCertificate n) :=
  smallestCertificate.equiv n hn
example : smallestTarget n = smallestExplicit n := rfl
example : smallestTarget n = smallestCertificate n := rfl
example : IsConic (smallestTarget n) := smallestTarget.isConic n
example : (smallestTarget.conicForm n).data.toProblem = smallestTarget n :=
  (smallestTarget.conicForm n).represents
example : (smallestTarget.conicForm n).data.rowCount = 1 := rfl

example (A : SymmetricMatrix n) (t : ℝ) : (smallestTarget n).feasible (A, t) ↔
    (A.toMatrix - t • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := Iff.rfl

example (p : FeasiblePoint (smallestTarget n)) :
    ((smallestTarget.equiv n hn).backward.map p).val = p.val := rfl

section AffineSmallest

-- Helpers expose the affine operand while retaining the minimum-eigenvalue atom.
def matrixPencil {n : Nat} (A₀ A₁ : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) := A₀ + x • A₁

def smallestValue {n : Nat} (A : Matrix (Fin n) (Fin n) ℝ) := Fn.lambdaMin A

open Lean Lean.Meta in
run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (n : Nat)
    (A : Matrix (Fin n) (Fin n) ℝ) => smallestValue A))
  lambdaBoundedTelescope expression 2 fun _ body => do
    let expanded ← Morew.Elab.Affine.Expansion.expand body fun value preserveLets =>
      Morew.Elab.Expr.reduceStructure value (preserveLets := preserveLets)
    unless expanded.isAppOf ``Fn.lambdaMin do
      throwError "helper expansion did not preserve the minimum-eigenvalue atom"
    unless ← isDefEq expanded body do
      throwError "helper expansion changed the minimum-eigenvalue expression"
    MorewTest.checkCompleteWithKernel expanded "incomplete minimum-eigenvalue helper expansion"

def affineSmallestSource (n : Nat) (A₀ A₁ : Matrix (Fin n) (Fin n) ℝ) :=
  problem (x t : ℝ)
    maximize t
    subject to bound : t + 1 ≤ Fn.lambdaMin (matrixPencil A₀ A₁ x)

variable (A₀ A₁ : Matrix (Fin n) (Fin n) ℝ) (hA₀ : A₀.IsSymm) (hA₁ : A₁.IsSymm)

reformulation affineSmallestTarget : (affineSmallestSource n A₀ A₁) := by conic

reformulation affineSmallestExplicit : (affineSmallestSource n A₀ A₁) := by
  conic at bound using (Spectral.lambdaMinHypograph hn)
  conic

example : GlobalEquiv (affineSmallestSource n A₀ A₁)
    (affineSmallestTarget n A₀ A₁ hA₀ hA₁) :=
  affineSmallestTarget.equiv n hn A₀ A₁ hA₀ hA₁
example : GlobalEquiv (affineSmallestSource n A₀ A₁)
    (affineSmallestExplicit n A₀ A₁ hA₀ hA₁) :=
  affineSmallestExplicit.equiv n hn A₀ A₁ hA₀ hA₁
example : affineSmallestTarget n A₀ A₁ hA₀ hA₁ =
    affineSmallestExplicit n A₀ A₁ hA₀ hA₁ := rfl
example : IsConic (affineSmallestTarget n A₀ A₁ hA₀ hA₁) :=
  affineSmallestTarget.isConic n A₀ A₁ hA₀ hA₁
example : (affineSmallestTarget.conicForm n A₀ A₁ hA₀ hA₁).data.toProblem =
    affineSmallestTarget n A₀ A₁ hA₀ hA₁ :=
  (affineSmallestTarget.conicForm n A₀ A₁ hA₀ hA₁).represents

example (x t : ℝ) : (affineSmallestTarget n A₀ A₁ hA₀ hA₁).feasible (x, t) ↔
    (A₀ + x • A₁ - (t + 1) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := Iff.rfl

end AffineSmallest

section SmallestObjective

def smallestObjective (n : Nat) (A₀ A₁ : SymmetricMatrix n) :=
  problem (x : ℝ)
    maximize Fn.lambdaMin (matrixPencil A₀.toMatrix A₁.toMatrix x)
    subject to
      lower : 0 ≤ x
      upper : x ≤ 1

variable (A₀ A₁ : SymmetricMatrix n)

reformulation smallestLift : (smallestObjective n A₀ A₁) := by
  hypograph t
  conic

example : GlobalEquiv (smallestObjective n A₀ A₁) (smallestLift n A₀ A₁) :=
  smallestLift.equiv n hn A₀ A₁
example : IsConic (smallestLift n A₀ A₁) := smallestLift.isConic n A₀ A₁
example : (smallestLift.conicForm n A₀ A₁).data.toProblem = smallestLift n A₀ A₁ :=
  (smallestLift.conicForm n A₀ A₁).represents
example : (smallestLift.conicForm n A₀ A₁).data.rowCount = 3 := rfl
example (x t : ℝ) : (smallestLift n A₀ A₁).objective (x, t) = t := rfl

example (x t : ℝ) : (smallestLift n A₀ A₁).feasible (x, t) ↔
    0 ≤ x ∧ x ≤ 1 ∧
      (A₀.toMatrix + x • A₁.toMatrix - t • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  change (0 ≤ x ∧ 0 ≤ 1 - x ∧
    (A₀.toMatrix + x • A₁.toMatrix - t • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ↔ _
  rw [sub_nonneg]

example (p : FeasiblePoint (smallestObjective n A₀ A₁)) :
    ((smallestLift.equiv n hn A₀ A₁).forward.map p).val =
      (p.val, Fn.lambdaMin (A₀.toMatrix + p.val • A₁.toMatrix)) := rfl

example (p : FeasiblePoint (smallestLift n A₀ A₁)) :
    ((smallestLift.equiv n hn A₀ A₁).backward.map p).val = p.val.1 := rfl

example {p : FeasiblePoint (smallestLift n A₀ A₁)}
    (hp : (smallestLift n A₀ A₁).IsGlobalOptimum p) :
    (smallestObjective n A₀ A₁).IsGlobalOptimum
      ((smallestLift.equiv n hn A₀ A₁).backward.map p) :=
  (smallestLift.equiv n hn A₀ A₁).map_isGlobalOptimum_backward hp

run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``smallestLift
    | Lean.throwError "missing minimum-eigenvalue presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `smallestLiftCopy
  Lean.Elab.Command.elabCommand (← `(def $name := $term))

example : smallestLiftCopy n A₀ A₁ = smallestLift n A₀ A₁ := rfl

end SmallestObjective

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
