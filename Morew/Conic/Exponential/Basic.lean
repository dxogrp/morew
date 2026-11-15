/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic.Exponential.Cone
import Morew.Fn.Exponential
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# Exact exponential-cone representations

Exponential, logarithm, entropy, relative-entropy, KL-divergence, log-sum-exp,
and softplus bounds represented by exponential cone constraints.
-/

namespace Morew.Conic.Exponential

/-- An exponential upper bound is a unit-perspective cone membership. -/
theorem exp_le_iff (a t : ℝ) : Real.exp a ≤ t ↔ (a, 1, t) ∈ EXP := by
  simp [Cone.mem_exponential]

/-- A logarithmic lower bound is exact on its positive domain. -/
theorem le_log_iff (a t : ℝ) (ha : 0 < a) :
    t ≤ Real.log a ↔ (t, 1, a) ∈ EXP := by
  rw [← exp_le_iff]
  exact Real.le_log_iff_exp_le ha

/-- At a zero first argument, the relative-entropy formula agrees with the cone boundary. -/
theorem relEntr_zero_le_iff (b t : ℝ) (hb : 0 ≤ b) :
    Fn.relEntr 0 b ≤ t ↔ (-t, 0, b) ∈ EXP := by
  simp [Fn.relEntr, Cone.mem_exponential, hb]

/-- Relative entropy has an exponential-cone epigraph for `a ≥ 0` and `b > 0`. -/
theorem relEntr_le_iff (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Fn.relEntr a b ≤ t ↔ (-t, a, b) ∈ EXP := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · subst a
    exact relEntr_zero_le_iff b t hb.le
  rw [Fn.relEntr, Cone.mem_exponential_of_pos _ _ _ hpos]
  rw [mul_comm a, ← le_div_iff₀ hpos,
    mul_comm a, ← le_div_iff₀ hpos, ← Real.le_log_iff_exp_le (div_pos hb hpos),
    Real.log_div hpos.ne' hb.ne', Real.log_div hb.ne' hpos.ne', neg_div]
  constructor <;> intro h <;> linarith

/-- Entropy has an exponential-cone hypograph on nonnegative inputs. -/
theorem le_negMulLog_iff (a t : ℝ) (ha : 0 ≤ a) :
    t ≤ Real.negMulLog a ↔ (t, a, 1) ∈ EXP := by
  calc
    t ≤ Real.negMulLog a ↔ Fn.relEntr a 1 ≤ -t := by
      rw [Fn.relEntr_one_right]
      exact neg_le_neg_iff.symm
    _ ↔ (t, a, 1) ∈ EXP := by
      simpa only [neg_neg] using relEntr_le_iff a 1 (-t) ha zero_lt_one

/-- The entropy atom has an exponential-cone hypograph on nonnegative inputs. -/
theorem le_entr_iff (a t : ℝ) (ha : 0 ≤ a) :
    t ≤ Fn.entr a ↔ (t, a, 1) ∈ EXP :=
  le_negMulLog_iff a t ha

/-- KL divergence has an exponential-cone epigraph for `a ≥ 0` and `b > 0`. -/
theorem klDiv_le_iff (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    Fn.klDiv a b ≤ t ↔ (b - a - t, a, b) ∈ EXP := by
  have hbound : Fn.klDiv a b ≤ t ↔ Fn.relEntr a b ≤ t + a - b := by
    rw [Fn.klDiv]
    constructor <;> intro h <;> linarith
  have hcoord : -(t + a - b) = b - a - t := by linarith
  rw [hbound, relEntr_le_iff a b (t + a - b) ha hb, hcoord]

/-- A finite entropy sum has a hypograph represented by one exponential cone
per coordinate and one affine sum bound. The empty sum is allowed. -/
theorem le_sum_entr_iff {n : Nat} (x : Fin n → ℝ) (t : ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    t ≤ ∑ i, Fn.entr (x i) ↔
      ∃ u : Fin n → ℝ, (∀ i, (u i, x i, 1) ∈ EXP) ∧ t ≤ ∑ i, u i := by
  constructor
  · intro h
    exact ⟨fun i => Fn.entr (x i), fun i => (le_entr_iff _ _ (hx i)).mp le_rfl, h⟩
  · rintro ⟨u, hu, hsum⟩
    exact hsum.trans (Finset.sum_le_sum fun i _ => (le_entr_iff _ _ (hx i)).mpr (hu i))

/-- A finite KL sum has an epigraph represented by one exponential cone per
coordinate and one affine sum bound. The empty sum is allowed. -/
theorem sum_klDiv_le_iff {n : Nat} (x q : Fin n → ℝ) (t : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hq : ∀ i, 0 < q i) :
    (∑ i, Fn.klDiv (x i) (q i)) ≤ t ↔
      ∃ u : Fin n → ℝ,
        (∀ i, (q i - x i - u i, x i, q i) ∈ EXP) ∧ (∑ i, u i) ≤ t := by
  constructor
  · intro h
    exact ⟨fun i => Fn.klDiv (x i) (q i),
      fun i => (klDiv_le_iff _ _ _ (hx i) (hq i)).mp le_rfl, h⟩
  · rintro ⟨u, hu, hsum⟩
    exact (Finset.sum_le_sum fun i _ =>
      (klDiv_le_iff _ _ _ (hx i) (hq i)).mpr (hu i)).trans hsum

/-- A nonempty finite log-sum-exp bound is represented by a family of
exponential-cone constraints and one affine sum bound. -/
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

end Morew.Conic.Exponential
