import PTran.Conic
import Mathlib.Tactic.NormNum

/-!
# Native polyhedral identities

The semantic import supplies exact bounds without importing the reformulation
language. Tests cover symbolic finite sets and dimensions, including empty
norm carriers and bounds below zero.
-/

assert_not_exists PTran.ExactConstraintLift PTran.Syntax.ProblemView

namespace PTranTest.Conic.Polyhedral

open PTran.Conic.Polyhedral
open scoped ENNReal

example (a t : ℝ) : |a| ≤ t ↔ a ≤ t ∧ -a ≤ t := abs_le_iff a t

example (a t : ℝ) : a⁺ ≤ t ↔ a ≤ t ∧ 0 ≤ t := posPart_le_iff a t

example (a b t : ℝ) : max a b ≤ t ↔ a ≤ t ∧ b ≤ t :=
  PTran.Conic.Polyhedral.max_le_iff a b t

example (a b t : ℝ) : t ≤ min a b ↔ t ≤ a ∧ t ≤ b :=
  PTran.Conic.Polyhedral.le_min_iff a b t

example (a : ℝ) : ¬ a⁺ ≤ -1 := by
  rw [posPart_le_iff]
  norm_num

example : max (-3 : ℝ) (-2) ≤ -1 := by
  rw [PTran.Conic.Polyhedral.max_le_iff]
  norm_num

example : (-3 : ℝ) ≤ min (-2) (-1) := by
  rw [PTran.Conic.Polyhedral.le_min_iff]
  norm_num

/-! Arbitrary nonempty finite sets do not require a finite ambient index type. -/

example (s : Finset ℕ) (hs : s.Nonempty) (a : ℕ → ℝ) (t : ℝ) :
    s.sup' hs a ≤ t ↔
      (fun j : Fin s.card => a (s.equivFin.symm j)) ≤ (fun _ => t) :=
  sup'_le_iff s hs a t

example {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ) (t : ℝ) :
    t ≤ s.inf' hs a ↔
      (fun _ : Fin s.card => t) ≤ (fun j => a (s.equivFin.symm j)) :=
  le_inf'_iff s hs a t

example (a : ℕ → ℝ) : ({4} : Finset ℕ).sup' (by simp) a = a 4 := by
  simp

example (a : ℕ → ℝ) : ({4} : Finset ℕ).inf' (by simp) a = a 4 := by
  simp

example {ι : Type*} : ¬ (∅ : Finset ι).Nonempty := Finset.not_nonempty_empty

/-! The ordinary function norm and explicit infinity norm retain zero bounds. -/

example (n : ℕ) (v : Fin n → ℝ) (t : ℝ) :
    ‖v‖ ≤ t ↔ 0 ≤ t ∧ v ≤ (fun _ => t) ∧ -v ≤ (fun _ => t) :=
  norm_le_iff v t

example (v : Fin 0 → ℝ) (t : ℝ) : ‖v‖ ≤ t ↔ 0 ≤ t := by
  rw [norm_le_iff]
  simp

example (v : Fin 0 → ℝ) : ¬ ‖v‖ ≤ -1 := by
  rw [norm_le_iff]
  norm_num

example (n : ℕ) (v : Fin n → ℝ) : ¬ ‖v‖ ≤ -1 := by
  rw [norm_le_iff]
  norm_num

example (a t : ℝ) : ‖fun _ : Fin 1 => a‖ ≤ t ↔ |a| ≤ t := by
  rw [norm_le_iff, abs_le_iff]
  simp only [Pi.le_def, Pi.neg_apply, Fin.forall_fin_one]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(abs_nonneg a).trans (abs_le'.mpr h), h⟩

example (v : Fin 0 → ℝ) (t : ℝ) : ‖WithLp.toLp ∞ v‖ ≤ t ↔ 0 ≤ t := by
  rw [norm_toLp_top_le_iff]
  simp

example (n : ℕ) (v : Fin n → ℝ) : ¬ ‖WithLp.toLp ∞ v‖ ≤ -1 := by
  rw [norm_toLp_top_le_iff]
  norm_num

/-! The one-norm uses a vector witness, with the empty sum retaining its bound. -/

example (n : ℕ) (v : Fin n → ℝ) (t : ℝ) :
    ‖WithLp.toLp 1 v‖ ≤ t ↔
      ∃ u : Fin n → ℝ, v ≤ u ∧ -v ≤ u ∧ (∑ i, u i) ≤ t :=
  norm_toLp_one_le_iff v t

example (v : Fin 0 → ℝ) (t : ℝ) : ‖WithLp.toLp 1 v‖ ≤ t ↔ 0 ≤ t := by
  rw [norm_toLp_one_le_iff]
  simp

example (v : Fin 0 → ℝ) : ¬ ‖WithLp.toLp 1 v‖ ≤ -1 := by
  rw [norm_toLp_one_le_iff]
  simp

example (n : ℕ) (v : Fin n → ℝ) : ¬ ‖WithLp.toLp 1 v‖ ≤ -1 := by
  intro h
  have := (norm_nonneg (WithLp.toLp 1 v)).trans h
  norm_num at this

example (a t : ℝ) : ‖WithLp.toLp 1 (fun _ : Fin 1 => a)‖ ≤ t ↔ |a| ≤ t := by
  rw [PiLp.norm_eq_of_L1]
  simp only [Real.norm_eq_abs, Fin.sum_univ_one]

example : ‖WithLp.toLp 1 (![2, -3] : Fin 2 → ℝ)‖ ≤ 5 := by
  rw [PiLp.norm_eq_of_L1]
  norm_num [Fin.sum_univ_succ, PiLp.toLp_apply]

end PTranTest.Conic.Polyhedral
