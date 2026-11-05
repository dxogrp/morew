/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Substitution
import Mathlib.Tactic.NormNum

/-!
# Semantic coordinate parameterization tests

Both equivalence maps preserve retained coordinates, including when coordinate
types differ or the selected coordinate lies inside a product. Surjectivity is
required only on feasible points.
-/

namespace MorewTest.Transform.Parameterization

open Morew CoordinateParameterization

private def positiveSource : Problem (ℝ × ℕ) ℝ where
  objective point := point.1
  feasible point := 0 ≤ point.1

private def subtypeRule :
    CoordinateParameterization (fun (_ : ℕ) (u : {x : ℝ // 0 ≤ x}) => u.1) where
  range _ x := 0 ≤ x
  preimage _ x := x
  rightInverse _ _ := rfl

private def subtypeCoverage := subtypeRule.toFeasibleSurjection positiveSource
  (Equiv.prodComm ℝ ℕ) (Equiv.prodComm {x : ℝ // 0 ≤ x} ℕ)
  (fun _ h => h)

/-- The new coordinate may have a different type. -/
example : GlobalEquivalence positiveSource
    (positiveSource.pullback fun point : {x : ℝ // 0 ≤ x} × ℕ => (point.1.1, point.2)) :=
  pullbackEquivalence positiveSource _ subtypeCoverage

example (point : FeasiblePoint positiveSource) :
    (subtypeCoverage.preimage point).2 = point.1.2 := rfl

example (point : {x : ℝ // 0 ≤ x} × ℕ) :
    (coordinateMap (fun (_ : ℕ) (u : {x : ℝ // 0 ≤ x}) => u.1)
      (Equiv.prodComm ℝ ℕ) (Equiv.prodComm {x : ℝ // 0 ≤ x} ℕ) point).2 =
        point.2 := rfl

private def dependentSource : Problem (ℝ × ℝ) ℝ where
  objective point := point.1 * point.2
  feasible point := point.1 ≠ 0 ∧ 0 ≤ point.2

private noncomputable def dependentCoverage :=
  (Substitution.mulLeft (fun a : ℝ => a)).toFeasibleSurjection dependentSource
    (Equiv.refl _) (Equiv.refl _) (fun _ h => h.1)

/-- The coefficient may vanish away from the feasible retained coordinates. -/
noncomputable example : GlobalEquivalence dependentSource
    (dependentSource.pullback fun point : ℝ × ℝ => (point.1, point.1 * point.2)) :=
  pullbackEquivalence dependentSource _ dependentCoverage

example (point : FeasiblePoint dependentSource) :
    dependentCoverage.preimage point = (point.1.1, point.1.2 / point.1.1) := rfl

private def middleSplit : (ℝ × ℝ × ℝ) ≃ (ℝ × ℝ) × ℝ where
  toFun point := ((point.1, point.2.2), point.2.1)
  invFun point := (point.1.1, point.2, point.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def middleSource : Problem (ℝ × ℝ × ℝ) (OrderDual ℝ) where
  objective point := point.1 + point.2.1 + point.2.2
  feasible point := 0 ≤ point.2.1

private noncomputable def middleCoverage :=
  Substitution.square.toFeasibleSurjection middleSource middleSplit middleSplit
    (fun _ h => h)

private noncomputable def middleEquivalence :=
  pullbackEquivalence middleSource
    (coordinateMap (fun (_ : ℝ × ℝ) (u : ℝ) => u ^ 2) middleSplit middleSplit)
    middleCoverage

example (point : FeasiblePoint middleSource) :
    (middleEquivalence.forward.map point).1 =
      (point.1.1, Real.sqrt point.1.2.1, point.1.2.2) := rfl

example (point : FeasiblePoint (middleSource.pullback
    (coordinateMap (fun (_ : ℝ × ℝ) (u : ℝ) => u ^ 2) middleSplit middleSplit))) :
    (middleEquivalence.backward.map point).1 =
      (point.1.1, point.1.2.1 ^ 2, point.1.2.2) := rfl

example : Substitution.square.preimage () ⟨0, le_rfl⟩ = 0 := Real.sqrt_zero

example : ¬ Function.Injective (fun u : ℝ => u ^ 2) := by
  intro h
  have impossible : (-1 : ℝ) = 1 := h (by norm_num)
  norm_num at impossible

example : ¬ (Substitution.affine (fun _ : Unit => (0 : ℝ)) (fun _ => 1)).range () 1 := by
  exact fun h => h rfl

/-- The public records expose their intended operation and exact coverage condition. -/
example (a b : ℝ → ℝ) (r x : ℝ) (h : a r ≠ 0) :
    a r * (Substitution.affine a b).preimage r ⟨x, h⟩ + b r = x :=
  (Substitution.affine a b).rightInverse r ⟨x, h⟩

example (x : ℝ) (h : 0 < x) :
    Real.exp (Substitution.exp.preimage () ⟨x, h⟩) = x :=
  Substitution.exp.rightInverse () ⟨x, h⟩

example (x : ℝ) (h : 0 ≤ x) :
    Substitution.square.preimage () ⟨x, h⟩ ^ 2 = x :=
  Substitution.square.rightInverse () ⟨x, h⟩

/-- No inverse outside the range, or even inhabited new type, is required. -/
private def emptyRule :
    CoordinateParameterization (fun (_ : Unit) (u : Empty) => (u.elim : Unit)) where
  range _ _ := False
  preimage _ x := x.2.elim
  rightInverse _ x := x.2.elim

private def infeasibleSource : Problem (Unit × Unit) ℕ where
  objective _ := 0
  feasible _ := False

example : FeasibleSurjection infeasibleSource
    (coordinateMap (fun (_ : Unit) (u : Empty) => (u.elim : Unit))
      (Equiv.refl _) (Equiv.refl _)) :=
  emptyRule.toFeasibleSurjection infeasibleSource
    (Equiv.refl _) (Equiv.refl _) (fun _ h => h)

end MorewTest.Transform.Parameterization
