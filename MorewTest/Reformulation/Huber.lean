/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Huber reformulation certificates

Automatic and explicit selection preserve the objective and surrounding rows.
An objective epigraph recovers the original decision and transfers optimality.
-/

namespace MorewTest.Reformulation.Huber

open Morew Morew.Conic

noncomputable section

def source (M : ℝ) :=
  problem (x t : ℝ)
    let residual := 2 * x - 1
    minimize t
    subject to
      before : -5 ≤ x
      loss : Fn.huber M residual ≤ t
      after : t ≤ 10

variable (M : ℝ) (hM : 0 ≤ M)

include hM in
reformulation targeted : (source M) := by
  conic at loss

include hM in
reformulation automatic : (source M) := by
  conic

reformulation selected : (source M) := by
  conic at loss using (SecondOrder.huberEpigraph M hM)
  conic

example : GlobalEquiv (source M) (targeted M) := targeted.equiv M hM
example : GlobalEquiv (source M) (automatic M) := automatic.equiv M hM
example : GlobalEquiv (source M) (selected M) := selected.equiv M hM
example : automatic M = selected M := rfl
example : IsConic (automatic M) := automatic.isConic M
example : (automatic.conicForm M).data.toProblem = automatic M :=
  (automatic.conicForm M).represents
example : (automatic.conicForm M).data.rowCount = 6 := rfl

example (x t z s r : ℝ) : (targeted M).objective ((x, t), z, s, r) = t := rfl

example (x t z s r : ℝ) : (targeted M).feasible ((x, t), z, s, r) ↔
    -5 ≤ x ∧ (s, 1 / 2, ![z]) ∈ RSOC 1 ∧
      -r ≤ 2 * x - 1 - z ∧ 2 * x - 1 - z ≤ r ∧ s + 2 * M * r ≤ t ∧
      t ≤ 10 := Iff.rfl

example (p : FeasiblePoint (automatic M)) :
    ((automatic.equiv M hM).backward.map p).val = p.val.1 := rfl

def objectiveSource (M : ℝ) :=
  problem (x : ℝ)
    minimize Fn.huber M (x - 1)

include hM in
reformulation objectiveTarget : (objectiveSource M) := by
  epigraph t
  conic

example : GlobalEquiv (objectiveSource M) (objectiveTarget M) := objectiveTarget.equiv M hM
example : IsConic (objectiveTarget M) := objectiveTarget.isConic M
example : (objectiveTarget.conicForm M).data.toProblem = objectiveTarget M :=
  (objectiveTarget.conicForm M).represents
example : (objectiveTarget.conicForm M).data.rowCount = 4 := rfl

example (p : FeasiblePoint (objectiveTarget M)) :
    ((objectiveTarget.equiv M hM).backward.map p).val = p.val.1.1 := rfl

example {p : FeasiblePoint (objectiveTarget M)}
    (hp : (objectiveTarget M).IsGlobalOptimum p) :
    (objectiveSource M).IsGlobalOptimum
      ((objectiveTarget.equiv M hM).backward.map p) :=
  (objectiveTarget.equiv M hM).map_isGlobalOptimum_backward hp

example : GlobalEquiv (objectiveSource 0) (objectiveTarget 0) :=
  objectiveTarget.equiv 0 (le_refl 0)

namespace FiniteSum

open scoped Matrix

def source (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (M : ℝ) :=
  problem (x : Fin n → ℝ)
    let residual := A *ᵥ x - b
    minimize ∑ i, Fn.huber M (residual i)

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (M : ℝ) (hM : 0 ≤ M)

include hM in
reformulation automatic : (source A b M) := by
  epigraph t as loss
  conic

reformulation selected : (source A b M) := by
  epigraph t as loss
  conic at loss using (SecondOrder.sumHuberEpigraph (n := m) M hM)
  conic

example : GlobalEquiv (source A b M) (automatic A b M) := automatic.equiv A b M hM
example : GlobalEquiv (source A b M) (selected A b M) := selected.equiv A b M hM
example : automatic A b M = selected A b M := rfl
example : IsConic (automatic A b M) := automatic.isConic A b M
example : (automatic.conicForm A b M).data.toProblem = automatic A b M :=
  (automatic.conicForm A b M).represents
example : (automatic.conicForm A b M).data.rowCount = 3 := rfl

example (x : Fin n → ℝ) (t : ℝ) (z u : Fin m → ℝ) :
    (automatic A b M).objective ((x, t), z, u) = t := rfl

example (p : FeasiblePoint (automatic A b M)) :
    ((automatic.equiv A b M hM).backward.map p).val = p.val.1.1 := rfl

example {p : FeasiblePoint (automatic A b M)}
    (hp : (automatic A b M).IsGlobalOptimum p) :
    (source A b M).IsGlobalOptimum ((automatic.equiv A b M hM).backward.map p) :=
  (automatic.equiv A b M hM).map_isGlobalOptimum_backward hp

example (x : Fin n → ℝ) : (source A b 0).objective x = 0 := by
  simp [source]

example : GlobalEquiv (source A b 0) (automatic A b 0) :=
  automatic.equiv A b 0 (le_refl 0)

example (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) (x : Fin n → ℝ) :
    (source A b M).objective x = 0 := by
  simp [source]

example (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) :
    GlobalEquiv (source A b M) (automatic A b M) := automatic.equiv A b M hM

example (A : Matrix (Fin m) (Fin 0) ℝ) : IsConic (automatic A b M) :=
  automatic.isConic A b M

end FiniteSum

end
end MorewTest.Reformulation.Huber
