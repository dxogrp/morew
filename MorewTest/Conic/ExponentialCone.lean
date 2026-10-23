import Morew.Conic.Exponential.Cone
import Mathlib.Tactic.NormNum

/-!
# Closed exponential cones and finite products

The cone module remains semantic-only. These examples check its exact boundary,
closedness, cone laws, and symbolic or empty products independently of automatic
atom rewriting.
-/

assert_not_exists Morew.ExactConstraintLift Morew.Syntax.ProblemView

namespace MorewTest.Conic.ExponentialCone

noncomputable section

open Morew.Conic

example : Cone.exponential.Space = (ℝ × ℝ × ℝ) := rfl
example : NormedAddCommGroup Cone.exponential.Space := inferInstance
example : NormedSpace ℝ Cone.exponential.Space := inferInstance
example : FiniteDimensional ℝ Cone.exponential.Space := inferInstance

example (n : Nat) : (Cone.exponentialProduct n).Space = (Fin n → (ℝ × ℝ × ℝ)) := rfl
example (n : Nat) : NormedAddCommGroup (Cone.exponentialProduct n).Space := inferInstance
example (n : Nat) : NormedSpace ℝ (Cone.exponentialProduct n).Space := inferInstance
example (n : Nat) : FiniteDimensional ℝ (Cone.exponentialProduct n).Space := inferInstance

example : EXP = Cone.exponential.carrier := rfl

example (x y z : ℝ) :
    (x, y, z) ∈ EXP ↔
      (0 < y ∧ y * Real.exp (x / y) ≤ z) ∨ (y = 0 ∧ x ≤ 0 ∧ 0 ≤ z) := by
  rw [Cone.mem_exponential]

example (x z : ℝ) : (x, 0, z) ∈ EXP ↔ x ≤ 0 ∧ 0 ≤ z := by simp

example (x y z : ℝ) (hy : 0 < y) :
    (x, y, z) ∈ EXP ↔ y * Real.exp (x / y) ≤ z :=
  Cone.mem_exponential_of_pos x y z hy

example (x y z : ℝ) (hy : y < 0) : (x, y, z) ∉ EXP :=
  Cone.not_mem_exponential_of_neg x y z hy

/-! The closed boundary includes the origin and the negative first-coordinate
ray, but excludes positive first coordinates and negative last coordinates. -/

example : ((0, 0, 0) : ℝ × ℝ × ℝ) ∈ EXP := by norm_num
example : ((-1, 0, 0) : ℝ × ℝ × ℝ) ∈ EXP := by norm_num
example : ((-2, 0, 3) : ℝ × ℝ × ℝ) ∈ EXP := by norm_num
example : ((1, 0, 1) : ℝ × ℝ × ℝ) ∉ EXP := by norm_num
example : ((-1, 0, -1) : ℝ × ℝ × ℝ) ∉ EXP := by norm_num
example : ((0, -1, 1) : ℝ × ℝ × ℝ) ∉ EXP := by norm_num
example : ((0, 1, 1) : ℝ × ℝ × ℝ) ∈ EXP := by norm_num
example : ((0, 1, 0) : ℝ × ℝ × ℝ) ∉ EXP := by norm_num

example : ((Real.log 2, 1, 2) : ℝ × ℝ × ℝ) ∈ EXP := by
  simp [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

example : Convex ℝ (↑EXP : Set Cone.exponential.Space) := Cone.exponential.carrier.convex
example : IsClosed (↑EXP : Set Cone.exponential.Space) := Cone.isClosed_exponential

example (p q : Cone.exponential.Space) (hp : p ∈ EXP) (hq : q ∈ EXP) :
    p + q ∈ EXP := Cone.exponential.carrier.add_mem hp hq

example (p : Cone.exponential.Space) (hp : p ∈ EXP) (c : ℝ) (hc : 0 < c) :
    c • p ∈ EXP := Cone.exponential.carrier.smul_mem hc hp

/-! Grouped membership supports symbolic dimensions and is universally true at
dimension zero. The product remains a closed convex cone in both cases. -/

example (n : Nat) (v : Fin n → (ℝ × ℝ × ℝ)) :
    v ∈ (Cone.exponentialProduct n).carrier ↔ ∀ i, v i ∈ EXP :=
  Cone.mem_exponentialProduct v

example (v : Fin 0 → (ℝ × ℝ × ℝ)) : v ∈ (Cone.exponentialProduct 0).carrier := by
  simp

example (x y z : ℝ) :
    (fun _ : Fin 1 => (x, y, z)) ∈ (Cone.exponentialProduct 1).carrier ↔
      (x, y, z) ∈ EXP := by
  simp

example (n : Nat) :
    (fun _ : Fin n => ((-1, 0, 0) : ℝ × ℝ × ℝ)) ∈
      (Cone.exponentialProduct n).carrier := by
  simp

example (n : Nat) :
    Convex ℝ (↑(Cone.exponentialProduct n).carrier : Set (Cone.exponentialProduct n).Space) :=
  (Cone.exponentialProduct n).carrier.convex

example (n : Nat) :
    IsClosed (↑(Cone.exponentialProduct n).carrier : Set (Cone.exponentialProduct n).Space) :=
  Cone.isClosed_exponentialProduct n

end

end MorewTest.Conic.ExponentialCone
