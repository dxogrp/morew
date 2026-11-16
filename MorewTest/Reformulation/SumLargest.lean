/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Conic

/-!
# Sum-largest reformulation certificates

Affine-vector bounds and lifted objectives retain exact conic forms. Recovery
projects away the threshold and slack variables, and the objective bound.
-/

namespace MorewTest.Reformulation.SumLargest

open Morew
open scoped Matrix

noncomputable section

def source (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Nat) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    let losses := A *ᵥ x - b
    minimize t
    subject to
      before : 0 ≤ x
      loss : Fn.sumLargest k losses ≤ t
      after : t ≤ 10

variable (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Nat) (hk : k ≤ m)

include hk in
reformulation targeted : (source A b k) := by
  conic at loss

include hk in
reformulation automatic : (source A b k) := by
  conic

reformulation selected : (source A b k) := by
  conic at loss using (Rewrite.sumLargestEpigraph k hk)
  conic

example : GlobalEquiv (source A b k) (targeted A b k) := targeted.equiv A b k hk
example : GlobalEquiv (source A b k) (automatic A b k) := automatic.equiv A b k hk
example : GlobalEquiv (source A b k) (selected A b k) := selected.equiv A b k hk
example : automatic A b k = selected A b k := rfl
example : IsConic (automatic A b k) := automatic.isConic A b k
example : (automatic.conicForm A b k).data.toProblem = automatic A b k :=
  (automatic.conicForm A b k).represents
example : (automatic.conicForm A b k).data.rowCount = 5 := rfl

example (x : Fin n → ℝ) (t τ : ℝ) (u : Fin m → ℝ) :
    (targeted A b k).objective ((x, t), τ, u) = t := rfl

example (x : Fin n → ℝ) (t τ : ℝ) (u : Fin m → ℝ) :
    (targeted A b k).feasible ((x, t), τ, u) ↔
      0 ≤ x ∧ 0 ≤ u ∧ A *ᵥ x - b - (fun _ => τ) ≤ u ∧
        (k : ℝ) * τ + (∑ i, u i) ≤ t ∧ t ≤ 10 := Iff.rfl

example (p : FeasiblePoint (automatic A b k)) :
    ((automatic.equiv A b k hk).backward.map p).val = p.val.1 := rfl

def objectiveSource (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (k : Nat) :=
  problem (x : Fin n → ℝ)
    let losses := A *ᵥ x - b
    minimize Fn.sumLargest k losses

include hk in
reformulation objectiveTarget : (objectiveSource A b k) := by
  epigraph t as loss
  conic

reformulation objectiveSelected : (objectiveSource A b k) := by
  epigraph t as loss
  conic at loss using (Rewrite.sumLargestEpigraph k hk)
  conic

example : GlobalEquiv (objectiveSource A b k) (objectiveTarget A b k) :=
  objectiveTarget.equiv A b k hk
example : GlobalEquiv (objectiveSource A b k) (objectiveSelected A b k) :=
  objectiveSelected.equiv A b k hk
example : objectiveTarget A b k = objectiveSelected A b k := rfl
example : IsConic (objectiveTarget A b k) := objectiveTarget.isConic A b k
example : (objectiveTarget.conicForm A b k).data.toProblem = objectiveTarget A b k :=
  (objectiveTarget.conicForm A b k).represents
example : (objectiveTarget.conicForm A b k).data.rowCount = 3 := rfl

example (x : Fin n → ℝ) (t τ : ℝ) (u : Fin m → ℝ) :
    (objectiveTarget A b k).objective ((x, t), τ, u) = t := rfl

example (p : FeasiblePoint (objectiveTarget A b k)) :
    ((objectiveTarget.equiv A b k hk).backward.map p).val = p.val.1.1 := rfl

example {p : FeasiblePoint (objectiveTarget A b k)}
    (hp : (objectiveTarget A b k).IsGlobalOptimum p) :
    (objectiveSource A b k).IsGlobalOptimum
      ((objectiveTarget.equiv A b k hk).backward.map p) :=
  (objectiveTarget.equiv A b k hk).map_isGlobalOptimum_backward hp

example : GlobalEquiv (objectiveSource A b 0) (objectiveTarget A b 0) :=
  objectiveTarget.equiv A b 0 (Nat.zero_le m)

example : GlobalEquiv (objectiveSource A b m) (objectiveTarget A b m) :=
  objectiveTarget.equiv A b m (le_refl m)

example (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) :
    GlobalEquiv (objectiveSource A b 0) (objectiveTarget A b 0) :=
  objectiveTarget.equiv A b 0 (le_refl 0)

example (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ) :
    (objectiveTarget.conicForm A b 0).data.rowCount = 3 := rfl

example (A : Matrix (Fin 0) (Fin n) ℝ) (b : Fin 0 → ℝ)
    (p : FeasiblePoint (objectiveTarget A b 0)) :
    0 ≤ (objectiveTarget A b 0).objective p := by
  simpa [objectiveSource] using
    (objectiveTarget.equiv A b 0 (le_refl 0)).backward.objective_le p

end
end MorewTest.Reformulation.SumLargest
