import PTran.Conic.Cone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The closed exponential cone

The exponential cone uses ordinary right-associated triples `(x, y, z)`.
Its positive branch is `y * exp (x / y) ≤ z`, and its zero-scale boundary
is `x ≤ 0 ∧ 0 ≤ z`. The boundary is part of the definition: replacing it
with totalized real division would describe a different set.

The cone laws and closedness follow from an equivalent intersection of
homogeneous closed halfspaces. Finite products certify grouped exponential
membership rows without expanding their coordinates or requiring a concrete
dimension.
-/

namespace PTran.Conic.Cone

private theorem exponential_tangent_bound (x y a : ℝ) (hy : 0 < y) :
    Real.exp a * (x + (1 - a) * y) ≤ y * Real.exp (x / y) := by
  calc
    Real.exp a * (x + (1 - a) * y)
        = (y * Real.exp a) * ((x / y - a) + 1) := by field_simp; ring
    _ ≤ (y * Real.exp a) * Real.exp (x / y - a) :=
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _)
        (mul_nonneg hy.le (Real.exp_nonneg _))
    _ = y * Real.exp (x / y) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

private theorem exponential_boundary_of_halfspaces (x z : ℝ)
    (h : ∀ a : ℝ, Real.exp a * x ≤ z) : x ≤ 0 ∧ 0 ≤ z := by
  have hc : ∀ r : ℝ, 0 < r → r * x ≤ z := by
    intro r hr
    simpa only [Real.exp_log hr] using h (Real.log r)
  have hx : x ≤ 0 := by
    by_contra hn
    have hx : 0 < x := lt_of_not_ge hn
    have hr : 0 < (|z| + 1) / x := div_pos (by positivity) hx
    have heq : ((|z| + 1) / x) * x = |z| + 1 := div_mul_cancel₀ _ (ne_of_gt hx)
    have hc' := hc _ hr
    rw [heq] at hc'
    linarith [le_abs_self z]
  refine ⟨hx, ?_⟩
  by_contra hn
  have hz : z < 0 := lt_of_not_ge hn
  have hden : x - 1 < 0 := by linarith
  have hr : 0 < z / (x - 1) := div_pos_of_neg_of_neg hz hden
  have heq : (z / (x - 1)) * (x - 1) = z := div_mul_cancel₀ _ (ne_of_lt hden)
  have hc' := hc _ hr
  nlinarith

private theorem exponential_iff_halfspaces (x y z : ℝ) :
    ((0 < y ∧ y * Real.exp (x / y) ≤ z) ∨ (y = 0 ∧ x ≤ 0 ∧ 0 ≤ z)) ↔
      0 ≤ y ∧ ∀ a : ℝ, Real.exp a * (x + (1 - a) * y) ≤ z := by
  constructor
  · rintro (⟨hy, hz⟩ | ⟨rfl, hx, hz⟩)
    · exact ⟨hy.le, fun a => (exponential_tangent_bound x y a hy).trans hz⟩
    · refine ⟨le_rfl, fun a => ?_⟩
      simpa only [mul_zero, add_zero] using
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg a) hx).trans hz
  · rintro ⟨hy, h⟩
    rcases eq_or_lt_of_le hy with hy | hy
    · subst y
      exact Or.inr ⟨rfl, exponential_boundary_of_halfspaces x z (by simpa using h)⟩
    · apply Or.inl
      refine ⟨hy, ?_⟩
      have heq : x + (1 - x / y) * y = y := by field_simp; ring
      have hxy := h (x / y)
      rw [heq] at hxy
      simpa only [mul_comm] using hxy

/-- The closed exponential cone in ordinary coordinates `(x, y, z)`.
Its zero-scale boundary is included explicitly. -/
noncomputable def exponential : Cone where
  Space := ℝ × ℝ × ℝ
  carrier := {
    carrier := {p | (0 < p.2.1 ∧ p.2.1 * Real.exp (p.1 / p.2.1) ≤ p.2.2) ∨
      (p.2.1 = 0 ∧ p.1 ≤ 0 ∧ 0 ≤ p.2.2)}
    smul_mem' := by
      intro c hc p hp
      apply (exponential_iff_halfspaces _ _ _).mpr
      obtain ⟨hy, h⟩ := (exponential_iff_halfspaces _ _ _).mp hp
      refine ⟨mul_nonneg hc.le hy, fun a => ?_⟩
      change Real.exp a * (c * p.1 + (1 - a) * (c * p.2.1)) ≤ c * p.2.2
      calc
        _ = c * (Real.exp a * (p.1 + (1 - a) * p.2.1)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (h a) hc.le
    add_mem' := by
      intro p hp q hq
      apply (exponential_iff_halfspaces _ _ _).mpr
      obtain ⟨hpy, hp⟩ := (exponential_iff_halfspaces _ _ _).mp hp
      obtain ⟨hqy, hq⟩ := (exponential_iff_halfspaces _ _ _).mp hq
      refine ⟨add_nonneg hpy hqy, fun a => ?_⟩
      change Real.exp a * (p.1 + q.1 + (1 - a) * (p.2.1 + q.2.1)) ≤ p.2.2 + q.2.2
      calc
        _ = Real.exp a * (p.1 + (1 - a) * p.2.1) +
            Real.exp a * (q.1 + (1 - a) * q.2.1) := by ring
        _ ≤ _ := add_le_add (hp a) (hq a) }

/-- Exponential cone membership includes its exact zero-scale boundary. -/
@[simp]
theorem mem_exponential (x y z : ℝ) :
    (x, y, z) ∈ exponential.carrier ↔
      (0 < y ∧ y * Real.exp (x / y) ≤ z) ∨ (y = 0 ∧ x ≤ 0 ∧ 0 ≤ z) :=
  Iff.rfl

/-- At zero scale, exponential cone membership retains both boundary signs. -/
theorem mem_exponential_zero (x z : ℝ) :
    (x, 0, z) ∈ exponential.carrier ↔ x ≤ 0 ∧ 0 ≤ z := by
  simp only [mem_exponential, lt_self_iff_false, false_and, true_and, false_or]

/-- At positive scale, only the exponential-perspective branch is possible. -/
theorem mem_exponential_of_pos (x y z : ℝ) (hy : 0 < y) :
    (x, y, z) ∈ exponential.carrier ↔ y * Real.exp (x / y) ≤ z := by
  simp only [mem_exponential, hy, true_and, ne_of_gt hy, false_and, or_false]

/-- Negative scales never belong to the exponential cone. -/
theorem not_mem_exponential_of_neg (x y z : ℝ) (hy : y < 0) :
    (x, y, z) ∉ exponential.carrier := by
  simp only [mem_exponential]
  rintro (⟨hy', _⟩ | ⟨hy', _⟩) <;> linarith

/-- The exponential cone is closed, including its zero-scale boundary. -/
theorem isClosed_exponential :
    IsClosed (↑exponential.carrier : Set exponential.Space) := by
  have heq : (↑exponential.carrier : Set exponential.Space) =
      {p | 0 ≤ p.2.1} ∩ ⋂ a : ℝ, {p | Real.exp a * (p.1 + (1 - a) * p.2.1) ≤ p.2.2} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
    exact exponential_iff_halfspaces _ _ _
  rw [heq]
  exact (isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_iInter fun _ => isClosed_le (by fun_prop) (by fun_prop))

/-- The finite product of exponential cones. Each coordinate is an ordinary
triple; the empty product contains its unique coordinate vector. -/
noncomputable def exponentialProduct (n : Nat) : Cone where
  Space := Fin n → (ℝ × ℝ × ℝ)
  carrier := {
    carrier := {v | ∀ i, v i ∈ exponential.carrier}
    smul_mem' := fun _ hc _ h i => exponential.carrier.smul_mem hc (h i)
    add_mem' := fun _ hp _ hq i => exponential.carrier.add_mem (hp i) (hq i) }

/-- Finite-product membership is a grouped family of exponential memberships. -/
@[simp]
theorem mem_exponentialProduct {n : Nat} (v : Fin n → (ℝ × ℝ × ℝ)) :
    v ∈ (exponentialProduct n).carrier ↔ ∀ i, v i ∈ exponential.carrier :=
  Iff.rfl

/-- The finite product of exponential cones is closed, also at dimension zero. -/
theorem isClosed_exponentialProduct (n : Nat) :
    IsClosed (↑(exponentialProduct n).carrier : Set (exponentialProduct n).Space) := by
  change IsClosed {v : Fin n → (ℝ × ℝ × ℝ) | ∀ i, v i ∈ exponential.carrier}
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_exponential.preimage (continuous_apply i)

end PTran.Conic.Cone

namespace PTran.Conic

set_option quotPrecheck false in
/-- The closed exponential cone carrier, in coordinates `(x, y, z)`. -/
notation:max (name := exponentialCarrier) "EXP" => PTran.Conic.Cone.exponential.carrier

end PTran.Conic
