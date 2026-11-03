/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform

/-!
# Certified coordinate parameterizations

A coordinate parameterization supplies a right inverse on a specified range.
To apply it to a problem, prove that every feasible source coordinate lies in
that range.
-/

namespace Morew

universe u v w x y z

/-- A reusable right inverse for one coordinate, possibly depending on the
coordinates retained by a substitution. -/
structure CoordinateParameterization
    {Retained : Type u} {New : Type v} {Old : Type w}
    (f : Retained → New → Old) where
  /-- Old values for which the record supplies a preimage. -/
  range : Retained → Old → Prop
  /-- Choose a new value for an old value in the certified range. -/
  preimage : ∀ r, {a : Old // range r a} → New
  /-- The chosen value recovers the original coordinate. -/
  rightInverse : ∀ r a, f r (preimage r a) = a.1

namespace CoordinateParameterization

variable {Retained : Type u} {New : Type v} {Old : Type w}
  {X : Type x} {Y : Type y} {V : Type z}

/-- Replace the selected coordinate and preserve every retained coordinate.
The equivalences describe where those coordinates sit in the complete source
and target decision spaces. -/
abbrev coordinateMap (f : Retained → New → Old)
    (sourceSplit : X ≃ Retained × Old) (targetSplit : Y ≃ Retained × New)
    (point : Y) : X :=
  sourceSplit.symm ((targetSplit point).1, f (targetSplit point).1 (targetSplit point).2)

theorem coordinateMap_retained (f : Retained → New → Old)
    (sourceSplit : X ≃ Retained × Old) (targetSplit : Y ≃ Retained × New)
    (point : Y) :
    (sourceSplit (coordinateMap f sourceSplit targetSplit point)).1 =
      (targetSplit point).1 := by
  simp only [coordinateMap, Equiv.apply_symm_apply]

theorem coordinateMap_selected (f : Retained → New → Old)
    (sourceSplit : X ≃ Retained × Old) (targetSplit : Y ≃ Retained × New)
    (point : Y) :
    (sourceSplit (coordinateMap f sourceSplit targetSplit point)).2 =
      f (targetSplit point).1 (targetSplit point).2 := by
  simp only [coordinateMap, Equiv.apply_symm_apply]

/-- Construct a feasible surjection from a coordinate parameterization and
proof that its range contains every feasible source coordinate. The substitution
and its chosen preimage preserve retained coordinates. -/
def toFeasibleSurjection {f : Retained → New → Old}
    (rule : CoordinateParameterization f) (p : Problem X V)
    (sourceSplit : X ≃ Retained × Old) (targetSplit : Y ≃ Retained × New)
    (coverage : ∀ point, p.feasible point →
      rule.range (sourceSplit point).1 (sourceSplit point).2) :
    FeasibleSurjection p (coordinateMap f sourceSplit targetSplit) where
  preimage point := targetSplit.symm
    ((sourceSplit point.1).1,
      rule.preimage (sourceSplit point.1).1
        ⟨(sourceSplit point.1).2, coverage point.1 point.2⟩)
  rightInverse point := by
    simp only [coordinateMap, Equiv.apply_symm_apply, rule.rightInverse]
    exact sourceSplit.symm_apply_apply point.1

@[simp]
theorem toFeasibleSurjection_preimage_retained {f : Retained → New → Old}
    (rule : CoordinateParameterization f) (p : Problem X V)
    (sourceSplit : X ≃ Retained × Old) (targetSplit : Y ≃ Retained × New)
    (coverage : ∀ point, p.feasible point →
      rule.range (sourceSplit point).1 (sourceSplit point).2)
    (point : FeasiblePoint p) :
    (targetSplit ((rule.toFeasibleSurjection p sourceSplit targetSplit coverage).preimage
      point)).1 = (sourceSplit point.1).1 := by
  simp only [toFeasibleSurjection, Equiv.apply_symm_apply]

end CoordinateParameterization

end Morew
