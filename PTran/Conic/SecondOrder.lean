import PTran.Conic.Cone
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Second-order cones and exact quadratic bounds

The second-order cone uses the Euclidean norm of an ordinary finite coordinate
vector. The rotated cone is the linear preimage of a second-order cone and uses
the convention `‖x‖² ≤ 2 * u * v`, with both scalar coordinates nonnegative.
The representation lemmas include dimension zero and require strict positivity
of the denominator for quadratic-over-linear bounds.
-/

namespace PTran.Conic

namespace Cone

/-- The second-order cone `{(t,x) | ‖x‖₂ ≤ t}` in ordinary coordinates. -/
noncomputable def secondOrder (n : Nat) : Cone where
  Space := ℝ × (Fin n → ℝ)
  carrier := {
    carrier := {p | ‖WithLp.toLp 2 p.2‖ ≤ p.1}
    smul_mem' := by
      intro c hc p hp
      change ‖WithLp.toLp 2 (c • p.2)‖ ≤ c * p.1
      rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hp hc.le
    add_mem' := by
      intro p hp q hq
      change ‖WithLp.toLp 2 (p.2 + q.2)‖ ≤ p.1 + q.1
      rw [WithLp.toLp_add]
      exact (norm_add_le _ _).trans (add_le_add hp hq) }

/-- Second-order cone membership is the Euclidean upper-bound predicate. -/
@[simp]
theorem mem_secondOrder {n : Nat} (t : ℝ) (x : Fin n → ℝ) :
    (t, x) ∈ (secondOrder n).carrier ↔ ‖WithLp.toLp 2 x‖ ≤ t :=
  Iff.rfl

/-- The linear coordinate change realizing a rotated second-order cone as a
preimage of the ordinary second-order cone. -/
noncomputable def rotatedSecondOrderMap (n : Nat) :
    (ℝ × ℝ × (Fin n → ℝ)) →ₗ[ℝ] (ℝ × (Fin (n + 1) → ℝ)) where
  toFun p := (p.1 + p.2.1, Fin.cons (p.1 - p.2.1) (fun i => Real.sqrt 2 * p.2.2 i))
  map_add' p q := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add]
      ring
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
        ring
      · simp
        ring
  map_smul' c p := by
    apply Prod.ext
    · simp
      ring
    · funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
        ring
      · simp
        ring

/-- The rotated second-order cone with convention `‖x‖₂² ≤ 2*u*v`.
It is constructed as a linear preimage, so its cone laws follow from those of
the second-order cone. -/
noncomputable def rotatedSecondOrder (n : Nat) : Cone where
  Space := ℝ × ℝ × (Fin n → ℝ)
  carrier := (secondOrder (n + 1)).carrier.comap (rotatedSecondOrderMap n)

private theorem rotated_norm_sq {n : Nat} (u v : ℝ) (x : Fin n → ℝ) :
    ‖WithLp.toLp 2 (Fin.cons (u - v) (fun i => Real.sqrt 2 * x i) :
      Fin (n + 1) → ℝ)‖ ^ 2 =
      (u - v) ^ 2 + 2 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ,
    EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Rotated second-order membership retains both nonnegative coordinates,
including when the vector has dimension zero. -/
@[simp]
theorem mem_rotatedSecondOrder {n : Nat} (u v : ℝ) (x : Fin n → ℝ) :
    (u, v, x) ∈ (rotatedSecondOrder n).carrier ↔
      0 ≤ u ∧ 0 ≤ v ∧ ‖WithLp.toLp 2 x‖ ^ 2 ≤ 2 * u * v := by
  change ‖WithLp.toLp 2 (Fin.cons (u - v) (fun i => Real.sqrt 2 * x i) :
    Fin (n + 1) → ℝ)‖ ≤ u + v ↔ _
  have hsq := rotated_norm_sq u v x
  have hnorm := norm_nonneg (WithLp.toLp 2 (Fin.cons (u - v)
    (fun i => Real.sqrt 2 * x i) : Fin (n + 1) → ℝ))
  have hx := sq_nonneg ‖WithLp.toLp 2 x‖
  constructor
  · intro h
    have hsum : 0 ≤ u + v := hnorm.trans h
    have hquad : ‖WithLp.toLp 2 x‖ ^ 2 ≤ 2 * u * v := by
      nlinarith [sq_le_sq₀ hnorm hsum |>.mpr h]
    have hu : 0 ≤ u := by
      by_contra hu
      have hu' : u < 0 := lt_of_not_ge hu
      have hv' : 0 < v := by linarith
      have huv := mul_neg_of_neg_of_pos hu' hv'
      nlinarith
    have hv : 0 ≤ v := by
      by_contra hv
      have hv' : v < 0 := lt_of_not_ge hv
      have hu' : 0 < u := by linarith
      have huv := mul_neg_of_pos_of_neg hu' hv'
      nlinarith
    exact ⟨hu, hv, hquad⟩
  · rintro ⟨hu, hv, hquad⟩
    nlinarith

end Cone

namespace SecondOrder

/-- A native finite Euclidean norm bound is a second-order cone row. -/
theorem norm_toLp_le_iff {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ≤ t ↔ (t, v) ∈ (Cone.secondOrder n).carrier :=
  (Cone.mem_secondOrder t v).symm

/-- Native Euclidean-space decisions use their ordinary coordinate vector. -/
theorem norm_le_iff {n : Nat} (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖z‖ ≤ t ↔ (t, WithLp.ofLp z) ∈ (Cone.secondOrder n).carrier :=
  Iff.rfl

/-- A squared Euclidean norm bound is a rotated-cone row with rational scaling. -/
theorem norm_toLp_sq_le_iff {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 2 v‖ ^ 2 ≤ t ↔
      (t, 1 / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier := by
  rw [Cone.mem_rotatedSecondOrder]
  constructor
  · intro h
    refine ⟨(sq_nonneg _).trans h, by norm_num, ?_⟩
    nlinarith
  · rintro ⟨_, _, h⟩
    nlinarith

/-- A native squared Euclidean norm uses its ordinary coordinates. -/
theorem norm_sq_le_iff {n : Nat} (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖z‖ ^ 2 ≤ t ↔
      (t, 1 / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder n).carrier :=
  norm_toLp_sq_le_iff (WithLp.ofLp z) t

/-- A full finite sum of coordinate squares is a rotated-cone row. -/
theorem sumSquares_le_iff {n : Nat} (v : Fin n → ℝ) (t : ℝ) :
    (∑ i, v i ^ 2) ≤ t ↔
      (t, 1 / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier := by
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using
    norm_toLp_sq_le_iff v t

/-- A scalar square uses a singleton vector and the same rational scaling. -/
theorem square_le_iff (a t : ℝ) :
    a ^ 2 ≤ t ↔ (t, 1 / 2, ![a]) ∈ (Cone.rotatedSecondOrder 1).carrier := by
  simpa using sumSquares_le_iff (![a] : Fin 1 → ℝ) t

/-- A positive denominator makes a Euclidean quadratic-over-linear bound
exactly equivalent to a rotated-cone row. -/
theorem norm_toLp_sq_div_le_iff {n : Nat} (v : Fin n → ℝ) (y t : ℝ) (hy : 0 < y) :
    ‖WithLp.toLp 2 v‖ ^ 2 / y ≤ t ↔
      (t, y / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier := by
  rw [div_le_iff₀ hy, Cone.mem_rotatedSecondOrder]
  constructor
  · intro h
    have ht : 0 ≤ t := by
      by_contra ht
      have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge ht) hy
      nlinarith [sq_nonneg ‖WithLp.toLp 2 v‖]
    refine ⟨ht, by positivity, ?_⟩
    nlinarith
  · rintro ⟨_, _, h⟩
    nlinarith

/-- Native Euclidean quadratic-over-linear bounds use ordinary coordinates. -/
theorem norm_sq_div_le_iff {n : Nat} (z : EuclideanSpace ℝ (Fin n)) (y t : ℝ)
    (hy : 0 < y) :
    ‖z‖ ^ 2 / y ≤ t ↔
      (t, y / 2, WithLp.ofLp z) ∈ (Cone.rotatedSecondOrder n).carrier :=
  norm_toLp_sq_div_le_iff (WithLp.ofLp z) y t hy

/-- A positive-denominator sum of squares is a rotated-cone row. -/
theorem sumSquares_div_le_iff {n : Nat} (v : Fin n → ℝ) (y t : ℝ) (hy : 0 < y) :
    (∑ i, v i ^ 2) / y ≤ t ↔
      (t, y / 2, v) ∈ (Cone.rotatedSecondOrder n).carrier := by
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply] using
    norm_toLp_sq_div_le_iff v y t hy

/-- A scalar quadratic-over-linear bound uses a singleton rotated-cone row. -/
theorem square_div_le_iff (a y t : ℝ) (hy : 0 < y) :
    a ^ 2 / y ≤ t ↔ (t, y / 2, ![a]) ∈ (Cone.rotatedSecondOrder 1).carrier := by
  simpa using sumSquares_div_le_iff (![a] : Fin 1 → ℝ) y t hy

end SecondOrder
end PTran.Conic
