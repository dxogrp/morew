/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import Morew.Reformulation.Conic

/-! Quadratic terminal certificates preserve objectives, directions, and recovery maps. -/

namespace MorewTest.Reformulation.TerminalQuadConic

open Morew Morew.Conic
open Matrix
noncomputable section

def shifted :=
  problem (x : ℝ)
    minimize (x - 3) ^ 2 + 7
    subject to bounds : 0 ≤ x ∧ x ≤ 5

reformulation shiftedTarget : shifted := by
  qconic

example : GlobalEquiv shifted shiftedTarget := shiftedTarget.equiv
example : QuadConic.Form shiftedTarget := shiftedTarget.quadConicForm
example : IsQuadConic shiftedTarget := shiftedTarget.isQuadConic
example : shiftedTarget.quadConicForm.data.toProblem = shiftedTarget :=
  shiftedTarget.quadConicForm.represents
example : shiftedTarget.quadConicForm.data.sense = .minimize := rfl
example : shiftedTarget.quadConicForm.data.rowCount = 2 := rfl
example : ConvexOn ℝ Set.univ shiftedTarget.objective :=
  shiftedTarget.quadConicForm.objective_convexOn rfl
example : Convex ℝ {x | shiftedTarget.feasible x} :=
  shiftedTarget.quadConicForm.feasibleSetConvex
example (x : ℝ) : shiftedTarget.objective x = (x - 3) ^ 2 + 7 := rfl
example (x : ℝ) : shiftedTarget.feasible x ↔ 0 ≤ x ∧ x ≤ 5 := by
  change (0 ≤ x ∧ 0 ≤ 5 - x) ↔ _
  rw [sub_nonneg]
example : shiftedTarget.quadConicForm.data.toProblem.objective 0 = 16 := by
  rw [shiftedTarget.quadConicForm.represents]
  change (0 - 3 : ℝ) ^ 2 + 7 = 16
  norm_num

def maximum :=
  problem (x : ℝ)
    maximize 10 - (x - 2) ^ 2
    subject to lower : 0 ≤ x

reformulation maximumTarget : maximum := by
  qconic

example : Problem ℝ (OrderDual ℝ) := maximumTarget
example : maximumTarget.quadConicForm.data.sense = .maximize := rfl
example : IsQuadConic maximumTarget := maximumTarget.isQuadConic
example : ConcaveOn (β := ℝ) ℝ Set.univ maximumTarget.objective :=
  maximumTarget.quadConicForm.objective_concaveOn rfl
example : GlobalEquiv maximum maximumTarget := maximumTarget.equiv
example : maximumTarget.quadConicForm.data.toProblem.objective 0 = 6 := by
  rw [maximumTarget.quadConicForm.represents]
  change 10 - (0 - 2 : ℝ) ^ 2 = 6
  norm_num

run_cmd Lean.Elab.Command.liftTermElabM do
  let type := (← Lean.getConstInfo ``maximumTarget).type
  unless type.isAppOfArity ``Morew.Problem 2 &&
      type.getAppArgs[1]!.isAppOfArity ``OrderDual 1 do
    throwError "maximizing quadratic target lost its explicit OrderDual annotation"
  let info ← Lean.getConstInfo ``shiftedTarget.isQuadConic
  let some value := info.value? (allowOpaque := true) | throwError "missing property proof"
  unless (value.find? (·.isConstOf ``shiftedTarget.quadConicForm)).isSome do
    throwError "the property did not reference the named quadratic form"

def affine (c : ℝ) := problem (x : ℝ) maximize c * x + 4

variable (c : ℝ)

reformulation affineTarget : (affine c) := by
  qconic

example (c : ℝ) : IsQuadConic (affineTarget c) := affineTarget.isQuadConic c
example (c : ℝ) : (affineTarget.quadConicForm c).data.sense = .maximize := rfl

section Division

variable (denominator : ℝ) (hdenominator : 0 < denominator)

def divided (denominator : ℝ) :=
  problem (x : ℝ)
    minimize (x - 1) ^ 2 / denominator + 3
    subject to lower : 0 ≤ x

include hdenominator in
reformulation dividedTarget : (divided denominator) := by qconic

example : GlobalEquiv (divided denominator) (dividedTarget denominator) :=
  dividedTarget.equiv denominator
example : IsQuadConic (dividedTarget denominator) :=
  dividedTarget.isQuadConic denominator hdenominator
example (x : ℝ) : (dividedTarget denominator).objective x =
    (x - 1) ^ 2 / denominator + 3 := rfl
example (x : ℝ) : (dividedTarget denominator).feasible x ↔ 0 ≤ x := Iff.rfl

end Division

section FiniteSums

variable (indices : Finset ℕ) (weight : ℕ → ℝ) (hweight : ∀ i ∈ indices, 0 < weight i)

def weightedSum (indices : Finset ℕ) (weight : ℕ → ℝ) :=
  problem (x : ℝ)
    minimize ∑ i ∈ indices, (x - i) ^ 2 / weight i

include hweight in
reformulation weightedSumTarget : (weightedSum indices weight) := by qconic

example : GlobalEquiv (weightedSum indices weight) (weightedSumTarget indices weight) :=
  weightedSumTarget.equiv indices weight
example : IsQuadConic (weightedSumTarget indices weight) :=
  weightedSumTarget.isQuadConic indices weight hweight
example : (weightedSumTarget indices weight).objective 0 =
    ∑ i ∈ indices, (i : ℝ) ^ 2 / weight i := by
  change (∑ i ∈ indices, (0 - (i : ℝ)) ^ 2 / weight i) = _
  simp

end FiniteSums

section DiagonalWeights

variable (weight : Fin n → Fin n → ℝ) (hweight : ∀ i j, 0 ≤ weight i j)

def diagonalSum (weight : Fin n → Fin n → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize ∑ i, weight i i * (x i)^2

include hweight in
reformulation diagonalSumTarget : (diagonalSum weight) := by qconic

example : GlobalEquiv (diagonalSum weight) (diagonalSumTarget weight) :=
  diagonalSumTarget.equiv weight
example : IsQuadConic (diagonalSumTarget weight) :=
  diagonalSumTarget.isQuadConic weight hweight
example (x : Fin n → ℝ) : (diagonalSumTarget weight).objective x =
    ∑ i, weight i i * (x i)^2 := rfl

end DiagonalWeights

def empty := problem (x : Fin 0 → ℝ) minimize Fn.norm2 x ^ 2 + 5
reformulation emptyTarget : empty := by qconic
example : emptyTarget.quadConicForm.data.rowCount = 0 := rfl
example (x : Fin 0 → ℝ) : emptyTarget.objective x = 5 := by
  change Fn.norm2 x ^ 2 + 5 = 5
  simp

def square := problem (x : ℝ) minimize (x - 3) ^ 2
reformulation squareTarget : square := by qconic
reformulation lifted : squareTarget := by
  epigraph t
  conic
example : IsConic lifted := lifted.isConic
example : GlobalEquiv square lifted := squareTarget.equiv.trans lifted.equiv

def nonlinearRows :=
  problem (x t : ℝ)
    minimize (x - 3) ^ 2 + 5 + t
    subject to
      quadratic : x ^ 2 ≤ t
      absolute : |x| ≤ 4

reformulation converted : nonlinearRows := by
  qconic
reformulation selected : nonlinearRows := by
  conic at quadratic
  qconic
example : converted.quadConicForm.data.rowCount = 3 := rfl
example : selected.quadConicForm.data.rowCount = 3 := rfl
example : GlobalEquiv nonlinearRows converted := converted.equiv
example : GlobalEquiv nonlinearRows selected := selected.equiv

section Auxiliaries

variable (weight : ℝ) (hweight : 0 ≤ weight)

def twoAuxiliaries (weight : ℝ) :=
  problem (x t : ℝ)
    minimize (x - 3) ^ 2 + weight * t ^ 2 + 7
    subject to
      first : Fn.softplus x ≤ t
      second : Fn.softplus (-x) ≤ t

include hweight in
reformulation auxiliaryTarget : (twoAuxiliaries weight) := by
  qconic

example : GlobalEquiv (twoAuxiliaries weight) (auxiliaryTarget weight) :=
  auxiliaryTarget.equiv weight
example : IsQuadConic (auxiliaryTarget weight) :=
  auxiliaryTarget.isQuadConic weight hweight
example : (auxiliaryTarget.quadConicForm weight hweight).data.rowCount = 4 := rfl
example (x t : ℝ) (u v : Fin 2 → ℝ) :
    (auxiliaryTarget weight).objective (((x, t), u), v) =
      (x - 3) ^ 2 + weight * t ^ 2 + 7 := rfl
example (z : FeasiblePoint (auxiliaryTarget weight)) :
    ((auxiliaryTarget.equiv weight).backward.map z).val = z.val.1.1 := rfl
example {z : FeasiblePoint (auxiliaryTarget weight)}
    (hz : (auxiliaryTarget weight).IsGlobalOptimum z) :
    (twoAuxiliaries weight).IsGlobalOptimum
      ((auxiliaryTarget.equiv weight).backward.map z) :=
  (auxiliaryTarget.equiv weight).map_isGlobalOptimum_backward hz
example (z : ((ℝ × ℝ) × (Fin 2 → ℝ)) × (Fin 2 → ℝ)) :
    (auxiliaryTarget.quadConicForm weight hweight).data.toProblem.feasible z ↔
      (auxiliaryTarget weight).feasible z := by
  rw [(auxiliaryTarget.quadConicForm weight hweight).represents]

end Auxiliaries

section Matrices

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
  (C : Matrix (Fin k) (Fin n) ℝ) (d : Fin k → ℝ) (weight : ℝ)
  (hweight : 0 ≤ weight)

def rectangular (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin k) (Fin n) ℝ) (d : Fin k → ℝ) (weight : ℝ) :=
  problem (x : Fin n → ℝ)
    let residual := A *ᵥ x - b
    minimize Fn.norm2 residual ^ 2 + weight * Fn.norm2 x ^ 2
    subject to balance : C *ᵥ x = d

include hweight in
reformulation rectangularTarget : (rectangular A b C d weight) := by qconic

example : GlobalEquiv (rectangular A b C d weight) (rectangularTarget A b C d weight) :=
  rectangularTarget.equiv A b C d weight
example : IsQuadConic (rectangularTarget A b C d weight) :=
  rectangularTarget.isQuadConic A b C d weight hweight
example (x : Fin n → ℝ) : (rectangularTarget A b C d weight).objective x =
    Fn.norm2 (A *ᵥ x - b) ^ 2 + weight * Fn.norm2 x ^ 2 := rfl
example (x : Fin n → ℝ) :
    (rectangularTarget A b C d weight).feasible x ↔ C *ᵥ x = d := by
  change C *ᵥ x - d = 0 ↔ C *ᵥ x = d
  exact sub_eq_zero

example : IsQuadConic
    (rectangularTarget (0 : Matrix (Fin 0) (Fin 0) ℝ) 0
      (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0) :=
  rectangularTarget.isQuadConic _ _ _ _ _ (le_refl 0)

example :
    (rectangularTarget (0 : Matrix (Fin 2) (Fin 0) ℝ) ![3, 4]
      (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0).objective 0 = 25 := by
  change Fn.norm2 ((0 : Matrix (Fin 2) (Fin 0) ℝ) *ᵥ 0 - ![3, 4]) ^ 2 +
    0 * Fn.norm2 (0 : Fin 0 → ℝ) ^ 2 = 25
  norm_num [Fn.norm2_sq_eq_sum, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Matrices

namespace MatrixForms

def named (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) :=
  problem (x : Fin n → ℝ)
    let residual := A *ᵥ x + b
    minimize Fn.quadForm residual Q + c ⬝ᵥ x + d
    subject to nonneg : x ∈ ℝ₊^n

def native (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) :=
  problem (x : Fin n → ℝ)
    let residual := A *ᵥ x + b
    minimize residual ⬝ᵥ (Q *ᵥ residual) + c ⬝ᵥ x + d
    subject to nonneg : x ∈ ℝ₊^n

def maximum (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) :=
  problem (x : Fin n → ℝ)
    maximize -Fn.quadForm (A *ᵥ x + b) Q + c ⬝ᵥ x + d

section

variable (Q : Matrix (Fin m) (Fin m) ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
  (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ) (hQ : Q.PosSemidef)

include hQ in
reformulation namedTarget : (named Q A b c d) := by qconic

include hQ in
reformulation nativeTarget : (native Q A b c d) := by qconic

include hQ in
reformulation maximumTarget : (maximum Q A b c d) := by qconic

example : namedTarget Q A b c d = nativeTarget Q A b c d := rfl
example : GlobalEquiv (named Q A b c d) (namedTarget Q A b c d) :=
  namedTarget.equiv Q A b c d
example : GlobalEquiv (native Q A b c d) (nativeTarget Q A b c d) :=
  nativeTarget.equiv Q A b c d
example : IsQuadConic (namedTarget Q A b c d) := namedTarget.isQuadConic Q A b c d hQ
example : IsQuadConic (nativeTarget Q A b c d) := nativeTarget.isQuadConic Q A b c d hQ
example : (namedTarget.quadConicForm Q A b c d hQ).data.toProblem = namedTarget Q A b c d :=
  (namedTarget.quadConicForm Q A b c d hQ).represents
example (x : Fin n → ℝ) : (namedTarget Q A b c d).objective x =
    Fn.quadForm (A *ᵥ x + b) Q + c ⬝ᵥ x + d := rfl
example (x : Fin n → ℝ) : (namedTarget Q A b c d).feasible x ↔ 0 ≤ x := Iff.rfl
example (p : FeasiblePoint (namedTarget Q A b c d)) :
    ((namedTarget.equiv Q A b c d).backward.map p).val = p.val := rfl
example : GlobalEquiv (maximum Q A b c d) (maximumTarget Q A b c d) :=
  maximumTarget.equiv Q A b c d
example : IsQuadConic (maximumTarget Q A b c d) := maximumTarget.isQuadConic Q A b c d hQ
example : (maximumTarget.quadConicForm Q A b c d hQ).data.sense = .maximize := rfl
example : (maximumTarget.quadConicForm Q A b c d hQ).data.toProblem = maximumTarget Q A b c d :=
  (maximumTarget.quadConicForm Q A b c d hQ).represents

private def singular : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]
private theorem singularPSD : singular.PosSemidef :=
  Matrix.PosSemidef.diagonal (by intro i; fin_cases i <;> norm_num)

example : IsQuadConic (namedTarget singular 1 ![1, 2] ![3, 4] 5) :=
  namedTarget.isQuadConic _ _ _ _ _ singularPSD
example : (namedTarget.quadConicForm singular 1 ![1, 2] ![3, 4] 5 singularPSD).data.toProblem.objective
    ![2, 3] = 32 := by
  rw [(namedTarget.quadConicForm singular 1 ![1, 2] ![3, 4] 5 singularPSD).represents]
  norm_num [namedTarget, Fn.quadForm, singular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

example : IsQuadConic (namedTarget (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 ![2, 3] 7) :=
  namedTarget.isQuadConic _ _ _ _ _ Matrix.PosSemidef.zero
example : (namedTarget (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 ![2, 3] 7).objective ![1, 2] = 15 := by
  norm_num [namedTarget, Fn.quadForm, dotProduct, Fin.sum_univ_succ]
example : (namedTarget singular (0 : Matrix (Fin 2) (Fin 0) ℝ) ![3, 4] 0 5).objective 0 = 14 := by
  norm_num [namedTarget, Fn.quadForm, singular, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end

def lifted (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize Fn.quadForm x P + t
    subject to loss : Fn.softplus (c ⬝ᵥ x) ≤ t

variable (P : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) (hP : P.PosSemidef)

include hP in
reformulation liftedTarget : (lifted P c) := by qconic

example : GlobalEquiv (lifted P c) (liftedTarget P c) := liftedTarget.equiv P c
example : IsQuadConic (liftedTarget P c) := liftedTarget.isQuadConic P c hP
example : (liftedTarget.quadConicForm P c hP).data.toProblem = liftedTarget P c :=
  (liftedTarget.quadConicForm P c hP).represents
example (x : Fin n → ℝ) (t : ℝ) (u : Fin 2 → ℝ) :
    (liftedTarget P c).objective ((x, t), u) = Fn.quadForm x P + t := rfl
example (p : FeasiblePoint (liftedTarget P c)) :
    ((liftedTarget.equiv P c).backward.map p).val = p.val.1 := rfl
example {p : FeasiblePoint (liftedTarget P c)} (hp : (liftedTarget P c).IsGlobalOptimum p) :
    (lifted P c).IsGlobalOptimum ((liftedTarget.equiv P c).backward.map p) :=
  (liftedTarget.equiv P c).map_isGlobalOptimum_backward hp

end MatrixForms

end
end MorewTest.Reformulation.TerminalQuadConic
