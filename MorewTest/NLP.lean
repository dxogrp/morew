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

variable [FiniteDimensional ℝ X]

example (data : Data X) (x : X) : data.toProblem.objective x = data.objective x := rfl
example (data : Data X) (x : X) :
    data.toProblem.feasible x ↔ ∀ i, (data.rows i).Holds x := Iff.rfl
example (data : Data X) (x : X) (h : data.toProblem.feasible x) : x ∈ data.domain :=
  data.feasible_mem_domain x h
example (data : Data X) (noRows : data.rowCount = 0) (x : X) : x ∈ data.domain := by
  apply data.feasible_mem_domain x
  intro i
  exact Fin.elim0 (Fin.cast noRows i)
example {p : Problem X ℝ} (form : Form p) : IsSmoothNLP p := form.isSmoothNLP

end Generic

/-! ## A nonconvex polynomial objective in both senses -/

def intervalRow : Row ℝ Set.univ where
  residual := fun x => x
  bounds := Bounds.between (-2) 2
  smooth := contDiffOn_id

def polynomialData : Data ℝ where
  sense := .minimize
  domain := Set.univ
  domain_isOpen := isOpen_univ
  objective := fun x => x ^ 4 - x ^ 2
  objective_smooth := ((contDiff_id.pow 4).sub (contDiff_id.pow 2)).contDiffOn
  rowCount := 1
  rows := fun _ => intervalRow
  feasible_mem_domain := fun _ _ => Set.mem_univ _

def polynomialProblem : Problem ℝ ℝ where
  objective := fun x => x ^ 4 - x ^ 2
  feasible := fun x => ∀ _ : Fin 1, intervalRow.Holds x

def polynomialForm : Form polynomialProblem where
  data := polynomialData
  represents := rfl

example : polynomialForm.data = polynomialData := rfl
example : polynomialForm.data.sense = .minimize := rfl
example : polynomialData.toProblem = polynomialProblem := polynomialForm.represents
example : IsSmoothNLP polynomialProblem := polynomialForm.isSmoothNLP
example (x : ℝ) : polynomialData.toProblem.objective x = x ^ 4 - x ^ 2 := rfl
example (x : ℝ) : polynomialData.toProblem.feasible x ↔ -2 ≤ x ∧ x ≤ 2 := by
  simp [polynomialData, intervalRow, Row.Holds]

def polynomialMaximumData : Data ℝ := { polynomialData with sense := .maximize }

-- Both the dual result type and the recorded sense stay explicit; the
-- objective is preserved instead of being negated.
def polynomialMaximum : Problem ℝ (OrderDual ℝ) where
  objective := fun x => x ^ 4 - x ^ 2
  feasible := fun x => ∀ _ : Fin 1, intervalRow.Holds x

def polynomialMaximumForm : Form polynomialMaximum where
  data := polynomialMaximumData
  represents := rfl

example : polynomialMaximumForm.data = polynomialMaximumData := rfl
example : polynomialMaximumForm.data.sense = .maximize := rfl
example : polynomialMaximumData.toProblem = polynomialMaximum := polynomialMaximumForm.represents
example : IsSmoothNLP polynomialMaximum := polynomialMaximumForm.isSmoothNLP
example (x : ℝ) : polynomialMaximumData.toProblem.objective x = x ^ 4 - x ^ 2 := rfl

/-! ## Nonlinear product rows and symbolic finite vectors -/

def productRow : Row (ℝ × ℝ) Set.univ where
  residual := fun x => x.1 * x.2 + x.2 ^ 2
  bounds := Bounds.fixed 1
  smooth := (contDiffOn_fst.mul contDiffOn_snd).add (contDiffOn_snd.pow 2)

def productData : Data (ℝ × ℝ) where
  sense := .minimize
  domain := Set.univ
  domain_isOpen := isOpen_univ
  objective := fun x => x.1 ^ 2 + x.2 ^ 2
  objective_smooth := (contDiffOn_fst.pow 2).add (contDiffOn_snd.pow 2)
  rowCount := 1
  rows := fun _ => productRow
  feasible_mem_domain := fun _ _ => Set.mem_univ _

example (x : ℝ × ℝ) : productData.toProblem.feasible x ↔ x.1 * x.2 + x.2 ^ 2 = 1 := by
  simp [productData, productRow, Row.Holds]
example : productData.toProblem.feasible (0, 1) := by
  norm_num [productData, productRow, Row.Holds]
example : ¬ productData.toProblem.feasible (0, 0) := by
  norm_num [productData, productRow, Row.Holds]

def vectorData (n : Nat) : Data (Fin n → ℝ) where
  sense := .minimize
  domain := Set.univ
  domain_isOpen := isOpen_univ
  objective := fun x => ∑ i, x i ^ 2
  objective_smooth := ContDiffOn.sum fun i _ => (contDiffOn_apply ℝ ℝ i _).pow 2
  rowCount := n
  rows := fun i => {
    residual := fun x => x i
    bounds := Bounds.lowerBound 0
    smooth := contDiffOn_apply ℝ ℝ i _
  }
  feasible_mem_domain := fun _ _ => Set.mem_univ _

example (n : Nat) (x : Fin n → ℝ) :
    (vectorData n).toProblem.feasible x ↔ ∀ i, 0 ≤ x i := by
  simp [vectorData, Row.Holds]
example (x : Fin 0 → ℝ) : (vectorData 0).toProblem.feasible x := by
  simp [vectorData]
example (x : Fin 0 → ℝ) : (vectorData 0).toProblem.objective x = 0 := by
  simp [vectorData]
example : (vectorData 3).toProblem.feasible (fun _ => 1) := by
  norm_num [vectorData, Row.Holds]

/-! ## Zero rows and empty evaluation domains -/

def unconstrainedData : Data ℝ where
  sense := .minimize
  domain := Set.univ
  domain_isOpen := isOpen_univ
  objective := fun _ => 4
  objective_smooth := contDiffOn_const
  rowCount := 0
  rows := Fin.elim0
  feasible_mem_domain := fun _ _ => Set.mem_univ _

example (x : ℝ) : unconstrainedData.toProblem.feasible x := by
  simp [unconstrainedData]
example (x : ℝ) : unconstrainedData.toProblem.objective x = 4 := rfl

def infeasibleRow : Row ℝ ∅ where
  residual := fun _ => 0
  bounds := Bounds.between 1 0
  smooth := contDiffOn_empty

def emptyDomainData : Data ℝ where
  sense := .minimize
  domain := ∅
  domain_isOpen := isOpen_empty
  objective := Real.log
  objective_smooth := contDiffOn_empty
  rowCount := 1
  rows := fun _ => infeasibleRow
  feasible_mem_domain := by
    intro x h
    have hrow := h 0
    norm_num [infeasibleRow, Row.Holds] at hrow

example (x : ℝ) : ¬ emptyDomainData.toProblem.feasible x := by
  simp [emptyDomainData, infeasibleRow, Row.Holds]
example (x : ℝ) : emptyDomainData.toProblem.objective x = Real.log x := rfl

/-! ## A proper domain and smoothness at every feasible point -/

def positiveRow : Row ℝ (Set.Ioi 0) where
  residual := fun x => x
  bounds := Bounds.lowerBound 1
  smooth := contDiffOn_id

def logData : Data ℝ where
  sense := .minimize
  domain := Set.Ioi 0
  domain_isOpen := isOpen_Ioi
  objective := Real.log
  objective_smooth := Real.contDiffOn_log.mono (by
    intro x hx
    exact ne_of_gt hx)
  rowCount := 1
  rows := fun _ => positiveRow
  feasible_mem_domain := by
    intro x h
    have hx : 1 ≤ x := by simpa [positiveRow, Row.Holds] using h 0
    exact lt_of_lt_of_le (by norm_num) hx

def logProblem : Problem ℝ ℝ where
  objective := Real.log
  feasible := fun x => ∀ _ : Fin 1, positiveRow.Holds x

def logForm : Form logProblem where
  data := logData
  represents := rfl

example : IsSmoothNLP logProblem := logForm.isSmoothNLP
example (x : ℝ) : logData.toProblem.feasible x ↔ 1 ≤ x := by
  simp [logData, positiveRow, Row.Holds]
example (x : ℝ) (hx : logData.toProblem.feasible x) :
    ContDiffAt ℝ 2 logData.objective x :=
  logData.objective_smooth.contDiffAt
    (logData.domain_isOpen.mem_nhds (logData.feasible_mem_domain x hx))
example (x : ℝ) (hx : logData.toProblem.feasible x) (i : Fin logData.rowCount) :
    ContDiffAt ℝ 2 (logData.rows i).residual x :=
  (logData.rows i).smooth.contDiffAt
    (logData.domain_isOpen.mem_nhds (logData.feasible_mem_domain x hx))

-- Exact representation still fixes objective values outside the open domain.
example : logData.toProblem.objective (-1) = Real.log (-1) := rfl
example : ¬ logData.toProblem.feasible 0 := by
  norm_num [logData, positiveRow, Row.Holds]

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

example : True := by
  fail_if_success
    let _ : Data ℝ := {
      sense := .minimize
      domain := Set.univ
      domain_isOpen := isOpen_univ
      objective := fun _ => 0
      rowCount := 0
      rows := Fin.elim0
      feasible_mem_domain := fun _ _ => Set.mem_univ _
    }
  trivial

example : True := by
  fail_if_success
    let _ : Data ℝ := {
      sense := .minimize
      domain := Set.univ
      objective := fun _ => 0
      objective_smooth := contDiffOn_const
      rowCount := 0
      rows := Fin.elim0
      feasible_mem_domain := fun _ _ => Set.mem_univ _
    }
  trivial

-- A closed feasible region does not supply the required open evaluation domain.
/--
error: Type mismatch
  isOpen_Ioi
has type
  IsOpen (Set.Ioi 0)
but is expected to have type
  IsOpen (Set.Icc (-2) 2)
-/
#guard_msgs in
example : Data ℝ := { polynomialData with
  domain := Set.Icc (-2) 2
  domain_isOpen := (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
  objective_smooth := ((contDiff_id.pow 4).sub (contDiff_id.pow 2)).contDiffOn
  rows := fun _ => {
    residual := fun x => x
    bounds := Bounds.between (-2) 2
    smooth := contDiffOn_id
  }
  feasible_mem_domain := fun _ h => h (0 : Fin 1)
}

-- Nonnegativity does not justify the strict positivity needed for log.
/--
error: Type mismatch: After simplification, term
  h 0
 has type
  0 ≤ x
but is expected to have type
  0 < x
-/
#guard_msgs in
example : Data ℝ := { logData with
  rows := fun _ => {
    residual := fun x => x
    bounds := Bounds.lowerBound 0
    smooth := contDiffOn_id
  }
  feasible_mem_domain := fun x h => by
    simpa [Row.Holds, logData] using h (0 : Fin 1)
}

example : True := by
  fail_if_success
    let _ : Data ℝ := {
      sense := .minimize
      domain := Set.univ
      domain_isOpen := isOpen_univ
      objective := fun _ => 0
      objective_smooth := contDiffOn_const
      rowCount := 0
      rows := Fin.elim0
    }
  trivial

-- Smoothness on a domain cannot replace equality of whole objective functions.
example : True := by
  fail_if_success
    let _ : Form (Problem.mk (fun _ : ℝ => (0 : ℝ)) emptyDomainData.toProblem.feasible) := {
      data := emptyDomainData
      represents := rfl
    }
  trivial

example : True := by
  fail_if_success
    let _ : Form polynomialProblem := { data := polynomialData }
  trivial

end

end MorewTest.NLP
