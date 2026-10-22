import PTran.Conic.Exponential.Cone
import PTran.Fn.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Exact exponential-cone representations

Exponential upper bounds need no domain assumptions. Logarithmic lower bounds
require a positive argument; relative-entropy upper bounds require a
nonnegative first argument and a positive second argument. These hypotheses
are essential because native real logarithm and division are totalized.

Finite log-sum-exp and softplus use one auxiliary finite vector, a grouped
family of exponential memberships, and one sum bound. Empty log-sum-exp is
excluded by an explicit dimension hypothesis. All results are semantic and
independent of elaboration or reformulation commands.
-/

namespace PTran.Conic.Exponential

/-- An exponential upper bound is a unit-perspective cone membership. -/
theorem exp_le_iff (a t : ℝ) : Real.exp a ≤ t ↔ (a, 1, t) ∈ EXP := by
  simp [Cone.mem_exponential]

/-- A logarithmic lower bound is exact on its positive domain. -/
theorem le_log_iff (a t : ℝ) (ha : 0 < a) :
    t ≤ Real.log a ↔ (t, 1, a) ∈ EXP := by
  rw [← exp_le_iff]
  exact Real.le_log_iff_exp_le ha

/-- Relative entropy at a zero first argument agrees with the closed cone's
boundary, including the corner where the second argument is also zero. -/
theorem relativeEntropy_zero_le_iff (b t : ℝ) (hb : 0 ≤ b) :
    Fn.relativeEntropy 0 b ≤ t ↔ (-t, 0, b) ∈ EXP := by
  simp [Fn.relativeEntropy, Cone.mem_exponential, hb]

/-- Relative entropy has an exact exponential-cone epigraph on its finite
domain. Nonnegativity, rather than positivity, retains the zero boundary. -/
theorem relativeEntropy_le_iff (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Fn.relativeEntropy a b ≤ t ↔ (-t, a, b) ∈ EXP := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst a
    exact relativeEntropy_zero_le_iff b t hb.le
  rw [Fn.relativeEntropy, Cone.mem_exponential]
  simp only [hpos, true_and, hpos.ne', false_and, or_false]
  rw [mul_comm a, ← le_div_iff₀ hpos,
    mul_comm a, ← le_div_iff₀ hpos, ← Real.le_log_iff_exp_le (div_pos hb hpos),
    Real.log_div hpos.ne' hb.ne', Real.log_div hb.ne' hpos.ne', neg_div]
  constructor <;> intro h <;> linarith

/-- A nonempty finite log-sum-exp bound is represented by exponential
memberships and one affine sum bound, with no coordinatewise scalar expansion. -/
theorem logSumExp_le_iff {n : Nat} (xs : Fin n → ℝ) (t : ℝ) (hn : 0 < n) :
    Fn.logSumExp xs ≤ t ↔
      ∃ u : Fin n → ℝ,
        (∀ i, (xs i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 := by
  have hs : 0 < ∑ i, Real.exp (xs i) :=
    Finset.sum_pos (fun i _ => Real.exp_pos (xs i))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hsum : (∑ i, Real.exp (xs i - t)) =
      (∑ i, Real.exp (xs i)) / Real.exp t := by
    simp only [Real.exp_sub, Finset.sum_div]
  rw [Fn.logSumExp, Real.log_le_iff_le_exp hs]
  constructor
  · intro h
    refine ⟨fun i => Real.exp (xs i - t), fun i => (exp_le_iff _ _).mp le_rfl, ?_⟩
    rw [hsum]
    exact (div_le_one (Real.exp_pos t)).mpr h
  · rintro ⟨u, hu, hsumu⟩
    have h : (∑ i, Real.exp (xs i - t)) ≤ 1 :=
      (Finset.sum_le_sum fun i _ => (exp_le_iff _ _).mpr (hu i)).trans hsumu
    rw [hsum] at h
    exact (div_le_one (Real.exp_pos t)).mp h

/-- Softplus is the two-term specialization of the finite representation. -/
theorem softplus_le_iff (a t : ℝ) :
    Fn.softplus a ≤ t ↔
      ∃ u : Fin 2 → ℝ,
        (∀ i : Fin 2, (![0, a] i - t, 1, u i) ∈ EXP) ∧ (∑ i, u i) ≤ 1 := by
  simpa [Fn.logSumExp, Fn.softplus, Fin.sum_univ_succ] using
    logSumExp_le_iff ![0, a] t (by decide : 0 < 2)

end PTran.Conic.Exponential
