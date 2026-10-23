import Morew.Transform.Context
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Real.Basic

/-!
# Semantic occurrence-bound certificates

These examples exercise distinct selected/objective types, dual objective
orders, assumptions available only on feasible points, and the forbidden
polarities for constraint lifting.
-/

namespace MorewTest.ObjectiveContext

open Morew

noncomputable section

/-- The selected value is natural, while the objective is integer-valued. -/
def naturalSource : Problem ℕ ℤ where
  objective n := (n : ℤ) + 1
  feasible n := 3 ≤ n

theorem naturalContext : ObjectiveEpigraphContext naturalSource
    (fun n => n) (fun _ a : ℕ => (a : ℤ) + 1) where
  atValue _ := rfl
  backward _ _ _ bound := add_le_add (Int.ofNat_le.mpr bound) le_rfl

def naturalEquivalence := objectiveEpigraphAtEquivalence naturalSource
  (fun n => n) (fun _ a : ℕ => (a : ℤ) + 1) naturalContext

example : naturalSource.IsGlobalOptimum ⟨3, le_rfl⟩ := by
  intro n
  exact add_le_add (Int.ofNat_le.mpr n.2) le_rfl

example : (naturalSource.epigraphAt (fun n => n)
    (fun _ a : ℕ => (a : ℤ) + 1)).IsGlobalOptimum
    (naturalEquivalence.forward.map ⟨3, le_rfl⟩) := by
  apply naturalEquivalence.map_isGlobalOptimum
  intro n
  exact add_le_add (Int.ofNat_le.mpr n.2) le_rfl

/-- Lower bounds at an objective occurrence use the dual objective order. -/
def maximumSource : Problem ℕ (OrderDual ℕ) where
  objective n := n
  feasible n := n ≤ 7

theorem maximumContext : ObjectiveHypographContext maximumSource
    (fun n => n) (fun _ a => a) where
  atValue _ := rfl
  backward _ _ _ bound := bound

def maximumEquivalence := objectiveHypographAtEquivalence maximumSource
  (fun n => n) (fun _ a => a) maximumContext

example : (maximumSource.hypographAt (fun n => n) (fun _ a => a)).HasGlobalOptimum := by
  apply maximumEquivalence.hasGlobalOptimum_iff.mp
  refine ⟨⟨7, le_rfl⟩, ?_⟩
  intro n
  exact n.2

/-- Objective monotonicity can depend on a source feasibility assumption. -/
def weightedSource : Problem (ℝ × ℝ) ℝ where
  objective point := point.1 * point.2
  feasible point := 0 ≤ point.1

theorem weightedContext : ObjectiveEpigraphContext weightedSource
    Prod.snd (fun point a => point.1 * a) where
  atValue _ := rfl
  backward _ feasible _ bound := mul_le_mul_of_nonneg_left bound feasible

example : GlobalEquivalence weightedSource
    (weightedSource.epigraphAt Prod.snd (fun point a => point.1 * a)) :=
  objectiveEpigraphAtEquivalence weightedSource Prod.snd (fun point a => point.1 * a)
    weightedContext

/-- Retained-row assumptions justify the same context inside a constraint. -/
def weightedConstraintSource : Problem (ℝ × ℝ) ℝ where
  objective point := point.2
  feasible point := 0 ≤ point.1 ∧ point.1 * point.2 ≤ 10

def weightedDecomposition : ConstraintDecomposition weightedConstraintSource
    (fun point => point.1 * point.2 ≤ 10) where
  remainder point := 0 ≤ point.1
  feasible_iff _ := Iff.rfl

theorem weightedConstraintContext : ConstraintBoundContext weightedDecomposition.remainder
    (fun point => point.1 * point.2 ≤ 10) Prod.snd
    (fun point a => point.1 * a ≤ 10) .upper where
  atValue _ := Iff.rfl
  backward _ retained _ bound target :=
    (mul_le_mul_of_nonneg_left bound retained).trans target

noncomputable def weightedConstraintEquivalence :=
  constraintBoundAtEquivalence weightedConstraintSource weightedDecomposition Prod.snd
    (fun point a => point.1 * a ≤ 10) .upper weightedConstraintContext

example (point : ℝ × ℝ) :
    weightedConstraintSource.feasible point ↔
      ∃ a : ℝ, (weightedConstraintSource.constraintBoundAt weightedDecomposition Prod.snd
        (fun point a => point.1 * a ≤ 10) .upper).feasible (point, a) :=
  weightedConstraintContext.toExactConstraintLift.source_iff_exists point

/-- An upper-bound constraint lift also works when the objective is maximized. -/
def maximumDecomposition : ConstraintDecomposition maximumSource (fun n => n ≤ 7) where
  remainder _ := True
  feasible_iff _ := ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

theorem maximumConstraintContext : ConstraintBoundContext maximumDecomposition.remainder
    (fun n => n ≤ 7) (fun n => n) (fun _ a => a ≤ 7) .upper where
  atValue _ := Iff.rfl
  backward _ _ _ bound target := bound.trans target

example : GlobalEquivalence maximumSource
    (maximumSource.constraintBoundAt maximumDecomposition
      (fun n => n) (fun _ a => a ≤ 7) .upper) :=
  constraintBoundAtEquivalence maximumSource maximumDecomposition
    (fun n => n) (fun _ a => a ≤ 7) .upper maximumConstraintContext

/-- The opposite predicate polarity cannot supply the required certificate. -/
example : ¬ Nonempty (ConstraintBoundContext (fun _ : ℕ => True)
    (fun n => 1 ≤ n) (fun n => n) (fun _ a => 1 ≤ a) .upper) := by
  rintro ⟨context⟩
  have impossible := context.backward 0 trivial 1 (by exact Nat.zero_le 1) (by decide)
  simp at impossible

/-- Replacing an equality by an upper bound would admit an extra source point. -/
example : ¬ Nonempty (ConstraintBoundContext (fun _ : ℕ => True)
    (fun n => n = 1) (fun n => n) (fun _ a => a = 1) .upper) := by
  rintro ⟨context⟩
  have impossible := context.backward 0 trivial 1 (by exact Nat.zero_le 1) rfl
  simp at impossible

end
end MorewTest.ObjectiveContext
