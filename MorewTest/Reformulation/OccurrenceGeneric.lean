import Morew.Reformulation
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Explicit occurrence certificates and generic selected values

Selected values can have a different ordered type from the objective. Explicit
certificates can use retained feasibility evidence without extending automatic
context recognition.
-/

namespace MorewTest.Reformulation.OccurrenceGeneric

open Morew
noncomputable section

def naturalSource :=
  problem (n : ℕ)
    let loss := n
    minimize (loss : ℤ) + 1

reformulation naturalTarget : naturalSource := by
  epigraph a at loss using (by
    refine { atValue := ?_, backward := ?_ }
    · intro point
      rfl
    · intro point _ auxiliary bound
      change point ≤ auxiliary at bound
      change (point : ℤ) + 1 ≤ (auxiliary : ℤ) + 1
      exact add_le_add (Int.ofNat_le.mpr bound) le_rfl)

example : GlobalEquivalence naturalSource naturalTarget := naturalTarget.equivalence
example (n a : ℕ) : naturalTarget.objective (n, a) = (a : ℤ) + 1 := rfl
example (n a : ℕ) : naturalTarget.feasible (n, a) ↔ n ≤ a := Iff.rfl

/--
info: problem (n a : ℕ)
  let loss := n
  minimize (↑a : ℤ) + 1
  subject to
    epigraph_a : loss ≤ a
-/
#guard_msgs in
#printp naturalTarget

def maximumSource :=
  problem (n : ℕ)
    let reward := n
    maximize (reward : ℤ) + 1
    subject to
      cap : n ≤ 7

reformulation maximumTarget : maximumSource := by
  hypograph a at reward using (by
    refine { atValue := ?_, backward := ?_ }
    · intro point
      rfl
    · intro point _ auxiliary bound
      change auxiliary ≤ point at bound
      change (auxiliary : ℤ) + 1 ≤ (point : ℤ) + 1
      exact add_le_add (Int.ofNat_le.mpr bound) le_rfl)

example : GlobalEquivalence maximumSource maximumTarget := maximumTarget.equivalence
example (n a : ℕ) : maximumTarget.feasible (n, a) ↔ n ≤ 7 ∧ a ≤ n := Iff.rfl

/--
info: problem (n a : ℕ)
  let reward := n
  maximize (↑a : ℤ) + 1
  subject to
    cap : n ≤ 7
    hypograph_a : a ≤ reward
-/
#guard_msgs in
#printp maximumTarget

def weightedSource :=
  problem (weight x : ℝ)
    let loss := x
    minimize x
    subject to
      nonnegative : 0 ≤ weight
      cap : weight * loss ≤ 10

reformulation weightedTarget : weightedSource := by
  epigraph a at loss in cap using (by
    refine { atValue := ?_, backward := ?_ }
    · intro point
      exact Iff.rfl
    · intro point retained auxiliary bound target
      change 0 ≤ point.1 at retained
      change point.2 ≤ auxiliary at bound
      change point.1 * auxiliary ≤ 10 at target
      exact (mul_le_mul_of_nonneg_left bound retained).trans target)

example : GlobalEquivalence weightedSource weightedTarget := weightedTarget.equivalence
example (weight x a : ℝ) : weightedTarget.feasible ((weight, x), a) ↔
    0 ≤ weight ∧ weight * a ≤ 10 ∧ x ≤ a := Iff.rfl

def dependentTypeSource :=
  problem (n : ℕ)
    let value : Fin (n + 1) := 0
    minimize value.val

/-- error: the selected type depends on a decision variable; dependent auxiliaries are unsupported -/
#guard_msgs (substring := true) in
reformulation dependentTypeTarget : dependentTypeSource := by
  epigraph a at value

def indexedSource :=
  problem (x : ℝ)
    minimize ∑ i : Fin 2, (x + (i.val : ℝ)) ^ 2

-- The index belongs to the sum's inner binder. A scalar occurrence selector
-- cannot capture it from the outer decision context.
/-- error: Unknown identifier `i.val` -/
#guard_msgs (substring := true) in
reformulation capturedIndex : indexedSource := by
  epigraph a at ((x + (i.val : ℝ)) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  for name in #[`dependentTypeTarget, `capturedIndex] do
    let full := `MorewTest.Reformulation.OccurrenceGeneric ++ name
    if env.contains full || (Morew.Syntax.getProblemView? env full).isSome then
      Lean.throwError "failed generic occurrence lift committed a declaration"

end
end MorewTest.Reformulation.OccurrenceGeneric
