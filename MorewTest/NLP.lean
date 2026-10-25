/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.NLP
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Manual smooth nonlinear programs

The semantic entry point supports checked smooth representations without
loading the modeling language or reformulation elaborator. The examples keep
the evaluation domain separate from the rows that define feasibility.
-/

assert_not_exists Morew.Syntax.ProblemView Morew.Elab.Reformulation.RunnerState

namespace MorewTest.NLP

open Morew Morew.NLP

universe u

noncomputable section

/-! ## Optional closed bounds -/

example (x : ℝ) : Bounds.unbounded.Contains x := by simp
example (l x : ℝ) : (Bounds.lowerBound l).Contains x ↔ l ≤ x := by simp
example (u x : ℝ) : (Bounds.upperBound u).Contains x ↔ x ≤ u := by simp
example (v x : ℝ) : (Bounds.fixed v).Contains x ↔ x = v := by simp
example (l u x : ℝ) : (Bounds.between l u).Contains x ↔ l ≤ x ∧ x ≤ u := by simp

example : (Bounds.between 1 3).Contains 1 := by norm_num
example : (Bounds.between 1 3).Contains 2 := by norm_num
example : (Bounds.between 1 3).Contains 3 := by norm_num
example : ¬ (Bounds.between 1 3).Contains 0 := by norm_num
example : ¬ (Bounds.between 1 3).Contains 4 := by norm_num
example : (Bounds.lowerBound 1).Contains 1 := by simp
example : (Bounds.upperBound 1).Contains 1 := by simp
example : (Bounds.fixed 2).Contains 2 := by simp
example : ¬ (Bounds.fixed 2).Contains 3 := by norm_num

-- Inconsistent endpoints are permitted data and describe an infeasible row.
example (x : ℝ) : ¬ (Bounds.between 1 0).Contains x := by
  simp only [Bounds.contains_between]
  intro h
  exact (not_le_of_gt (show (0 : ℝ) < 1 by norm_num)) (h.1.trans h.2)

/-! ## Universe-polymorphic semantics -/

section Generic

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

-- Rows do not require finite dimensionality, and domain membership is not a
-- conjunct of the row predicate.
example {domain : Set X} (row : Row X domain) (x : X) :
    row.Holds x ↔ row.bounds.Contains (row.residual x) := Iff.rfl

end Generic

/-! ## Missing and mismatched evidence is rejected -/

example : True := by
  fail_if_success
    let _ : Row ℝ Set.univ := { residual := Real.log, bounds := Bounds.unbounded }
  trivial

example : True := by
  fail_if_success
    let _ : Row ℝ Set.univ := {
      residual := Real.log
      bounds := Bounds.unbounded
      smooth := Real.contDiffOn_log
    }
  trivial

end

end MorewTest.NLP
