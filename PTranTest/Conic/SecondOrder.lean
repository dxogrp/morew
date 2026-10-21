import PTran.Conic
import Mathlib.Tactic.NormNum

/-!
# Exact second-order cone representations

The narrow semantic entry point exposes both cones and all native bounds without
installing the DSL. These tests exercise the factor-of-two convention, native
Euclidean coordinates, positive denominator evidence, and empty vectors.
-/

assert_not_exists PTran.ExactConstraintLift PTran.Syntax.ProblemView

namespace PTranTest.Conic.SecondOrder

noncomputable section

open PTran.Conic
open PTran.Conic.SecondOrder

example (n : Nat) : NormedAddCommGroup (Cone.secondOrder n).Space := inferInstance
example (n : Nat) : NormedSpace ℝ (Cone.secondOrder n).Space := inferInstance
example (n : Nat) : FiniteDimensional ℝ (Cone.secondOrder n).Space := inferInstance
example (n : Nat) : NormedAddCommGroup (Cone.rotatedSecondOrder n).Space := inferInstance
example (n : Nat) : NormedSpace ℝ (Cone.rotatedSecondOrder n).Space := inferInstance
example (n : Nat) : FiniteDimensional ℝ (Cone.rotatedSecondOrder n).Space := inferInstance

example (n : Nat) : (Cone.secondOrder n).Space = (ℝ × (Fin n → ℝ)) := rfl
example (n : Nat) : (Cone.rotatedSecondOrder n).Space = (ℝ × ℝ × (Fin n → ℝ)) := rfl

/-! The public notation denotes the carrier, with the vector dimension unchanged. -/

example (n : Nat) : SOC n = (Cone.secondOrder n).carrier := rfl
example (n : Nat) : RSOC n = (Cone.rotatedSecondOrder n).carrier := rfl

example (n : Nat) (t : ℝ) (x : Fin (n + 1) → ℝ) :
    (t, x) ∈ SOC (n + 1) ↔ (t, x) ∈ (Cone.secondOrder (n + 1)).carrier := Iff.rfl

example (u v : ℝ) (x : Fin 0 → ℝ) :
    (u, v, x) ∈ RSOC 0 ↔ (u, v, x) ∈ (Cone.rotatedSecondOrder 0).carrier := Iff.rfl

example (n : Nat) : Convex ℝ (↑(Cone.secondOrder n).carrier : Set (Cone.secondOrder n).Space) :=
  (Cone.secondOrder n).carrier.convex

example (n : Nat) :
    Convex ℝ (↑(Cone.rotatedSecondOrder n).carrier : Set (Cone.rotatedSecondOrder n).Space) :=
  (Cone.rotatedSecondOrder n).carrier.convex

example (n : Nat) (t : ℝ) (x : Fin n → ℝ) :
    (t, x) ∈ (Cone.secondOrder n).carrier ↔ ‖WithLp.toLp 2 x‖ ≤ t := by
  simp

example (n : Nat) (u v : ℝ) (x : Fin n → ℝ) :
    (u, v, x) ∈ (Cone.rotatedSecondOrder n).carrier ↔
      0 ≤ u ∧ 0 ≤ v ∧ ‖WithLp.toLp 2 x‖ ^ 2 ≤ 2 * u * v := by
  simp

/-! Native coordinate vectors and Euclidean decisions share the same exact rows. -/

example (n : Nat) (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ (t, v) ∈ (Cone.secondOrder n).carrier :=
  norm_toLp_le_iff v t

example (n : Nat) (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖z‖ ≤ t ↔ (t, WithLp.ofLp z) ∈ (Cone.secondOrder n).carrier :=
  norm_le_iff z t

example (a t : ℝ) :
    a ^ 2 ≤ t ↔ (t, 1 / 2, ![a]) ∈ (Cone.rotatedSecondOrder 1).carrier :=
  square_le_iff a t

example (n : Nat) (v : Fin n → ℝ) (t : ℝ) :
    (∑ i, v i ^ 2) ≤ t ↔ (t, 1 / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier :=
  sumSquares_le_iff v t

example (n : Nat) (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖z‖ ^ 2 ≤ t ↔
      (t, 1 / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder n).carrier :=
  norm_sq_le_iff z t

example (n : Nat) (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ^ 2 ≤ t ↔
      (t, 1 / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier :=
  norm_toLp_sq_le_iff v t

/-! Strict positivity is explicit evidence, also for zero-dimensional quotients. -/

example (a y t : ℝ) (hy : 0 < y) :
    a ^ 2 / y ≤ t ↔ (t, y / 2, ![a]) ∈ (Cone.rotatedSecondOrder 1).carrier :=
  square_div_le_iff a y t hy

example (n : Nat) (v : Fin n → ℝ) (y t : ℝ) (hy : 0 < y) :
    (∑ i, v i ^ 2) / y ≤ t ↔
      (t, y / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier :=
  sumSquares_div_le_iff v y t hy

example (n : Nat) (z : EuclideanSpace ℝ (Fin n)) (y t : ℝ) (hy : 0 < y) :
    ‖z‖ ^ 2 / y ≤ t ↔
      (t, y / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder n).carrier :=
  norm_sq_div_le_iff z y t hy

example (n : Nat) (v : Fin n → ℝ) (y t : ℝ) (hy : 0 < y) :
    ‖WithLp.toLp 2 v‖ ^ 2 / y ≤ t ↔
      (t, y / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier :=
  norm_toLp_sq_div_le_iff v y t hy

example (v : Fin 0 → ℝ) (t : ℝ) :
    (t, v) ∈ (Cone.secondOrder 0).carrier ↔ 0 ≤ t := by
  have hv : WithLp.toLp 2 v = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  rw [Cone.mem_secondOrder, hv, norm_zero]

example (v : Fin 0 → ℝ) (a b : ℝ) :
    (a, b, v) ∈ (Cone.rotatedSecondOrder 0).carrier ↔ 0 ≤ a ∧ 0 ≤ b := by
  have hv : WithLp.toLp 2 v = (0 : EuclideanSpace ℝ (Fin 0)) := Subsingleton.elim _ _
  rw [Cone.mem_rotatedSecondOrder, hv, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, mul_nonneg (mul_nonneg (by norm_num) h.1) h.2⟩⟩

example (v : Fin 0 → ℝ) (t : ℝ) :
    (∑ i, v i ^ 2) ≤ t ↔ 0 ≤ t := by simp

example (v : Fin 0 → ℝ) (y t : ℝ) (hy : 0 < y) :
    (t, y / 2, v) ∈ (Cone.rotatedSecondOrder 0).carrier ↔ 0 ≤ t := by
  rw [← sumSquares_div_le_iff v y t hy]
  simp

example (n : Nat) (v : Fin n → ℝ) :
    ¬ (-1, v) ∈ (Cone.secondOrder n).carrier := by
  rw [Cone.mem_secondOrder]
  exact not_le.mpr (lt_of_lt_of_le (by norm_num) (norm_nonneg _))

example (n : Nat) (v : Fin n → ℝ) :
    ¬ (-1, 1 / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier := by simp

example (n : Nat) (v : Fin n → ℝ) :
    ¬ (1, -1, v) ∈ (Cone.rotatedSecondOrder n).carrier := by simp

/-! Concrete boundary points detect the rotated cone's exact scaling. -/

example : (5, ![3, 4]) ∈ (Cone.secondOrder 2).carrier := by
  rw [Cone.mem_secondOrder]
  have hs : ‖WithLp.toLp 2 (![3, 4] : Fin 2 → ℝ)‖ ^ 2 = 25 := by
    norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  nlinarith [norm_nonneg (WithLp.toLp 2 (![3, 4] : Fin 2 → ℝ))]

example : (1, 2, ![2]) ∈ (Cone.rotatedSecondOrder 1).carrier := by
  norm_num [EuclideanSpace.real_norm_sq_eq]

example : ¬ (1, 1, ![2]) ∈ (Cone.rotatedSecondOrder 1).carrier := by
  norm_num [EuclideanSpace.real_norm_sq_eq]

example : (9, 1 / 2, ![3]) ∈ (Cone.rotatedSecondOrder 1).carrier := by
  rw [← square_le_iff]
  norm_num

example : (5, 5 / 2, ![3, 4]) ∈ (Cone.rotatedSecondOrder 2).carrier := by
  rw [← sumSquares_div_le_iff _ 5 5 (by norm_num)]
  norm_num [Fin.sum_univ_succ]

/-! Removing denominator positivity would change the feasible set. -/

example : (1 : ℝ) ^ 2 / 0 ≤ 0 := by norm_num

example : ¬ (0, 0 / 2, ![(1 : ℝ)]) ∈ (Cone.rotatedSecondOrder 1).carrier := by
  norm_num [EuclideanSpace.real_norm_sq_eq]

example : (1 : ℝ) ^ 2 / (-1) ≤ 0 := by norm_num

example : ¬ (0, (-1) / 2, ![(1 : ℝ)]) ∈ (Cone.rotatedSecondOrder 1).carrier := by
  norm_num

end
end PTranTest.Conic.SecondOrder
