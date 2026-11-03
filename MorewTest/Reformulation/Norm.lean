/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Reformulation.PrintDetails

/-! # Named vector norms reuse exact conic and smooth-NLP representations -/

namespace MorewTest.Reformulation.Norm

open Morew Morew.Conic
open Matrix

noncomputable section

def source (n : Nat) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      one : Fn.norm1 x ≤ t
      two : Fn.norm2 x ≤ t
      infinity : Fn.normInf x ≤ t

variable (n : Nat)

reformulation conicTarget : (source n) := by conic
reformulation nlpTarget : (source n) := by nlp

example : IsConic (conicTarget n) := conicTarget.isConic n
example : IsSmoothNLP (nlpTarget n) := nlpTarget.isSmoothNLP n
example : (conicTarget.conicForm n).data.rowCount = 7 := rfl
example : (nlpTarget.nlpForm 2).data.rowCount = 12 := rfl
example : (conicTarget.conicForm n).data.toProblem = conicTarget n :=
  (conicTarget.conicForm n).represents
example : (nlpTarget.nlpForm n).data.toProblem = nlpTarget n :=
  (nlpTarget.nlpForm n).represents
example : GlobalEquivalence (source n) (conicTarget n) := conicTarget.equivalence n
example : GlobalEquivalence (source n) (nlpTarget n) := nlpTarget.equivalence n

-- Explicit selection accepts both names and applied records. The targeted
-- intermediate remains available for imported continuation.
reformulation selected : (source n) := by
  conic at one using (Rewrite.fnNorm1Epigraph (n := n))
  conic at two using Conic.SecondOrder.fnNorm2Epigraph
  conic at infinity using Rewrite.fnNormInfEpigraph

reformulation selectedNLP : (source n) := by
  nlp at one using Rewrite.fnNorm1Epigraph
  nlp at two using (Rewrite.fnNorm2Epigraph (n := n))
  nlp at infinity using Rewrite.fnNormInfEpigraph

example (x u : Fin n → ℝ) (t : ℝ) :
    (selected n).feasible ((x, t), u) ↔
      x ≤ u ∧ -x ≤ u ∧ ∑ i, u i ≤ t ∧
      (t, x) ∈ (Cone.secondOrder n).carrier ∧
      0 ≤ t ∧ x ≤ (fun _ => t) ∧ -x ≤ (fun _ => t) := Iff.rfl

example (x u : Fin n → ℝ) (t : ℝ) :
    (selectedNLP n).feasible ((x, t), u) ↔
      x ≤ u ∧ -x ≤ u ∧ ∑ i, u i ≤ t ∧
      0 ≤ t ∧ ∑ i, x i ^ 2 ≤ t ^ 2 ∧
      0 ≤ t ∧ x ≤ (fun _ => t) ∧ -x ≤ (fun _ => t) := Iff.rfl

example (t : ℝ) : (selectedNLP 0).feasible ((Fin.elim0, t), Fin.elim0) ↔ 0 ≤ t := by
  simp [selectedNLP, sq_nonneg]
example : (selectedNLP 0).feasible ((Fin.elim0, 0), Fin.elim0) := by
  simp [selectedNLP]
example : ¬ (selectedNLP 0).feasible ((Fin.elim0, -1), Fin.elim0) := by
  simp [selectedNLP]
example : ¬ (selected 0).feasible ((Fin.elim0, -1), Fin.elim0) := by
  simp [selected]

-- Check each empty-dimensional representation separately: a guard retained by
-- a neighboring norm must not conceal a missing scalar bound.
example (t : ℝ) :
    (∃ u, (Rewrite.fnNorm1Epigraph (n := 0)).target Fin.elim0 t u) ↔ 0 ≤ t := by
  simp [Rewrite.fnNorm1Epigraph, Rewrite.norm1Epigraph]
example (t : ℝ) :
    (∃ u, (Rewrite.fnNormInfEpigraph (n := 0)).target Fin.elim0 t u) ↔ 0 ≤ t := by
  simp [Rewrite.fnNormInfEpigraph, Rewrite.normInfEpigraph]
example (t : ℝ) :
    (∃ u, (Rewrite.fnNorm2Epigraph (n := 0)).target Fin.elim0 t u) ↔ 0 ≤ t := by
  simp [Rewrite.fnNorm2Epigraph, Rewrite.norm2Epigraph, sq_nonneg]
example (t : ℝ) :
    (∃ u, (Conic.SecondOrder.fnNorm2Epigraph (n := 0)).target Fin.elim0 t u) ↔ 0 ≤ t := by
  rw [← Conic.SecondOrder.fnNorm2Epigraph.source_iff_exists]
  simp only [Fn.norm2_empty]

def residual (m n : Nat) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    let error := A *ᵥ x - b
    minimize Fn.norm2 error

-- The smooth coordinate checker already supports explicit finite sums. Its
-- recognition of matrix operations is independent of the named norm rules.
def residualCoordinates (m n : Nat) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :=
  problem (x : Fin n → ℝ)
    minimize Fn.norm2 (fun i => (∑ j, A i j * x j) - b i)

section Rectangular
variable (m : Nat) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

reformulation residualConic : (residual m n A b) := by
  epigraph t
  conic

reformulation residualNLP : (residualCoordinates m n A b) := by
  epigraph t
  nlp

example : IsConic (residualConic n m A b) := residualConic.isConic n m A b
example : IsSmoothNLP (residualNLP n m A b) := residualNLP.isSmoothNLP n m A b
example : (residualConic.conicForm n m A b).data.rowCount = 1 := rfl
example : residualCoordinates m n A b = residual m n A b := rfl
example : GlobalEquivalence (residual m n A b) (residualNLP n m A b) :=
  residualNLP.equivalence n m A b
end Rectangular

def negativeObjective :=
  problem (x : Fin 2 → ℝ)
    maximize -Fn.norm1 x

reformulation negativeConic : negativeObjective := by
  hypograph t
  conic

reformulation negativeNLP : negativeObjective := by
  hypograph t
  nlp

example : GlobalEquivalence negativeObjective negativeConic := negativeConic.equivalence
example : GlobalEquivalence negativeObjective negativeNLP := negativeNLP.equivalence
example : negativeConic.conicForm.data.sense = .maximize := rfl
example : negativeNLP.nlpForm.data.sense = .maximize := rfl

def nonlinear :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t ^ 2
    subject to
      one : Fn.norm1 (fun i => (x i) ^ 2) ≤ t
      two : Fn.norm2 (fun i => Real.sin (x i)) ≤ t
      infinity : Fn.normInf (fun i => Real.exp (x i)) ≤ t

reformulation nonlinearNLP : nonlinear := by nlp
example : IsSmoothNLP nonlinearNLP := nonlinearNLP.isSmoothNLP

/--
info: problem (x : Fin n → ℝ) (t : ℝ)
  minimize t
  subject to
    one : Fn.norm1 x ≤ t
    two : Fn.norm2 x ≤ t
    infinity : Fn.normInf x ≤ t
-/
#guard_msgs in
#printp source

run_cmd do
  let printed ← PrintDetails.printed ``selected false
  unless printed == (← PrintDetails.printed ``selected false) &&
      printed.contains "one_aux" && printed.contains "SOC n" &&
      printed.contains "infinity_conic_1" do
    Lean.throwError "named norm lowering changed its deterministic presentation: {printed}"

-- Named functions capture the library's norm instances, even when callers
-- install incompatible norms for the underlying finite functions and carriers.
section ShadowNorm
local instance : Norm (Fin 2 → ℝ) := ⟨fun _ => 37⟩
local instance : Norm (WithLp 1 (Fin 2 → ℝ)) := ⟨fun _ => 41⟩
local instance : Norm (EuclideanSpace ℝ (Fin 2)) := ⟨fun _ => 43⟩

def shadowed :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      one : Fn.norm1 x ≤ t
      two : Fn.norm2 x ≤ t
      infinity : Fn.normInf x ≤ t

example : shadowed = source 2 := rfl
reformulation shadowedConic : shadowed := by conic
reformulation shadowedNLP : shadowed := by nlp
example : GlobalEquivalence shadowed shadowedConic := shadowedConic.equivalence
example : GlobalEquivalence shadowed shadowedNLP := shadowedNLP.equivalence
end ShadowNorm

end
end MorewTest.Reformulation.Norm
