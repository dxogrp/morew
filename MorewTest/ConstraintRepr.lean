/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Transform
import Mathlib.Data.Real.Basic

/-!
# Exact auxiliary-variable constraint representations

Test the semantic API independently of the reformulation command and its metadata.
-/

namespace MorewTest.ConstraintRepr

open Morew

noncomputable section

/-! A pointwise equivalence gives an exact representation with `Unit` auxiliary data. -/

def zeroSymmetryRepr : ConstraintRepr (fun x : ℤ => x = 0) :=
  ConstraintRepr.ofIff
    (fun x : ℤ => 0 = x)
    fun x =>
      ⟨fun h : x = 0 => h.symm, fun h : 0 = x => h.symm⟩

example : zeroSymmetryRepr.Auxiliary = Unit := rfl

example (x : ℤ) :
    zeroSymmetryRepr.target x () ↔ 0 = x :=
  Iff.rfl

/-! A one-auxiliary representation of the epigraph of the square function. -/

def squareEpigraphRepr :
    EpigraphRepr (fun x : ℤ => x ^ 2) where
  Auxiliary := ℤ
  target x t a := a = x ^ 2 ∧ a ≤ t
  source_iff_exists x t := by
    constructor
    · intro h
      exact ⟨x ^ 2, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

def squareConstraintRepr :
    ConstraintRepr (fun point : ℤ × ℤ => point.1 ^ 2 ≤ point.2) :=
  squareEpigraphRepr.toConstraintRepr Prod.fst Prod.snd

def squareBoundProblem : Problem (ℤ × ℤ) ℤ where
  objective point := point.1 + point.2
  feasible point := point.1 ≤ 10 ∧ point.1 ^ 2 ≤ point.2

def squareBoundDecomposition :
    ConstraintDecomposition squareBoundProblem
      (fun point : ℤ × ℤ => point.1 ^ 2 ≤ point.2) where
  remainder point := point.1 ≤ 10
  feasible_iff _ := Iff.rfl

def replacedSquareBoundProblem : Problem ((ℤ × ℤ) × ℤ) ℤ :=
  squareBoundProblem.replaceConstraint
    squareConstraintRepr
    (decomposition := squareBoundDecomposition)

def squareBoundEquiv :
    GlobalEquiv squareBoundProblem replacedSquareBoundProblem :=
  replaceConstraintEquiv
    squareBoundProblem
    squareConstraintRepr
    squareBoundDecomposition

def squareBoundPoint : FeasiblePoint squareBoundProblem :=
  ⟨(2, 4), by
    change (2 : ℤ) ≤ 10 ∧ (2 : ℤ) ^ 2 ≤ 4
    decide⟩

example :
    (squareBoundEquiv.forward.map squareBoundPoint).1.1 =
      squareBoundPoint.1 :=
  rfl

example :
    replacedSquareBoundProblem.objective
        (squareBoundEquiv.forward.map squareBoundPoint).1 =
      squareBoundProblem.objective squareBoundPoint.1 :=
  rfl

example (point : FeasiblePoint replacedSquareBoundProblem) :
    (squareBoundEquiv.backward.map point).1 = point.1.1 :=
  rfl

example (point : FeasiblePoint replacedSquareBoundProblem) :
    squareBoundProblem.objective
        (squareBoundEquiv.backward.map point).1 =
      replacedSquareBoundProblem.objective point.1 :=
  rfl

/-! Graph conversion works for both orientations of the graph equation, and
hypograph conversion preserves its inequality orientation. -/

def successorGraphRepr :
    GraphRepr (fun x : ℤ => x + 1) where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists x y := by
    constructor
    · intro h
      exact ⟨(), h⟩
    · rintro ⟨_, h⟩
      exact h

example : ConstraintRepr
    (fun point : ℤ × ℤ => point.2 = point.1 + 1) :=
  successorGraphRepr.toConstraintRepr Prod.fst Prod.snd

example : ConstraintRepr
    (fun point : ℤ × ℤ => point.1 + 1 = point.2) :=
  successorGraphRepr.toConstraintReprSymm Prod.fst Prod.snd

example : ConstraintRepr
    (fun point : ℤ => point = (point - 1) + 1) :=
  successorGraphRepr.toConstraintRepr (fun point => point - 1) id

def squareHypographRepr :
    HypographRepr (fun x : ℤ => x ^ 2) where
  Auxiliary := Unit
  target x t _ := t ≤ x ^ 2
  source_iff_exists x t := by
    constructor
    · intro h
      exact ⟨(), h⟩
    · rintro ⟨_, h⟩
      exact h

example : ConstraintRepr
    (fun point : ℤ × ℤ => point.2 ≤ point.1 ^ 2) :=
  squareHypographRepr.toConstraintRepr Prod.fst Prod.snd

/-! Auxiliary values need not be unique. -/

def nonuniqueProductRepr : ConstraintRepr (fun x : ℤ => x = 0) where
  Auxiliary := ℤ × Bool
  target x _ := x = 0
  source_iff_exists x := by
    constructor
    · intro h
      exact ⟨(0, false), h⟩
    · rintro ⟨_, h⟩
      exact h

example :
    nonuniqueProductRepr.target 0 (0, false) ∧
      nonuniqueProductRepr.target 0 (1, true) ∧
      ((0 : ℤ), false) ≠ (1, true) := by
  simp [nonuniqueProductRepr]

/-! Infeasibility is transported in both directions by the equivalence. -/

def impossibleRepr : ConstraintRepr (fun _ : ℤ => False) :=
  ConstraintRepr.ofIff (fun _ : ℤ => False) fun _ => Iff.rfl

def impossibleProblem : Problem ℤ ℤ where
  objective x := x
  feasible _ := True ∧ False

def impossibleDecomposition :
    ConstraintDecomposition impossibleProblem (fun _ : ℤ => False) where
  remainder _ := True
  feasible_iff _ := Iff.rfl

def replacedImpossibleProblem : Problem (ℤ × Unit) ℤ :=
  impossibleProblem.replaceConstraint
    impossibleRepr
    impossibleDecomposition

def impossibleEquiv :
    GlobalEquiv impossibleProblem replacedImpossibleProblem :=
  replaceConstraintEquiv
    impossibleProblem
    impossibleRepr
    impossibleDecomposition

example :
    impossibleProblem.HasFeasiblePoint ↔
      replacedImpossibleProblem.HasFeasiblePoint :=
  impossibleEquiv.hasFeasiblePoint_iff

example : ¬ replacedImpossibleProblem.HasFeasiblePoint := by
  intro h
  have sourceHasPoint : impossibleProblem.HasFeasiblePoint :=
    impossibleEquiv.hasFeasiblePoint_iff.mpr h
  obtain ⟨point⟩ := sourceHasPoint
  exact point.2.2

/-! No convexity premise is needed, including for a disconnected feasible
set such as `x² = 1`. -/

def nonconvexProblem : Problem ℝ ℝ where
  objective x := x
  feasible x := True ∧ x ^ 2 = 1

def nonconvexRepr : ConstraintRepr (fun x : ℝ => x ^ 2 = 1) :=
  ConstraintRepr.ofIff
    (fun x : ℝ => x * x = 1)
    fun x => by
      simp only [pow_two]

def nonconvexDecomposition :
    ConstraintDecomposition nonconvexProblem
      (fun x : ℝ => x ^ 2 = 1) where
  remainder _ := True
  feasible_iff _ := Iff.rfl

def replacedNonconvexProblem :=
  nonconvexProblem.replaceConstraint
    nonconvexRepr
    nonconvexDecomposition

example : GlobalEquiv nonconvexProblem replacedNonconvexProblem :=
  replaceConstraintEquiv
    nonconvexProblem
    nonconvexRepr
    nonconvexDecomposition

/-! Independently certified representations compose by transitivity. -/

def twoConstraintProblem : Problem ℤ ℤ where
  objective x := x
  feasible x := x ≤ 0 ∧ x = 0

def firstSequentialRepr : ConstraintRepr (fun x : ℤ => x = 0) :=
  ConstraintRepr.ofIff
    (fun x : ℤ => 0 = x)
    fun x =>
      ⟨fun h : x = 0 => h.symm, fun h : 0 = x => h.symm⟩

def firstSequentialDecomposition :
    ConstraintDecomposition twoConstraintProblem
      (fun x : ℤ => x = 0) where
  remainder x := x ≤ 0
  feasible_iff _ := Iff.rfl

def afterFirstReplacement : Problem (ℤ × Unit) ℤ :=
  twoConstraintProblem.replaceConstraint
    firstSequentialRepr
    firstSequentialDecomposition

def firstSequentialEquiv :
    GlobalEquiv twoConstraintProblem afterFirstReplacement :=
  replaceConstraintEquiv
    twoConstraintProblem
    firstSequentialRepr
    firstSequentialDecomposition

def secondSequentialRepr :
    ConstraintRepr (fun point : ℤ × Unit => 0 = point.1) :=
  ConstraintRepr.ofIff
    (fun point : ℤ × Unit => point.1 = 0)
    fun point =>
      ⟨fun h : 0 = point.1 => h.symm, fun h : point.1 = 0 => h.symm⟩

def secondSequentialDecomposition :
    ConstraintDecomposition afterFirstReplacement
      (fun point : ℤ × Unit => 0 = point.1) where
  remainder point := point.1 ≤ 0
  feasible_iff _ := Iff.rfl

def afterSecondReplacement : Problem ((ℤ × Unit) × Unit) ℤ :=
  afterFirstReplacement.replaceConstraint
    secondSequentialRepr
    secondSequentialDecomposition

def secondSequentialEquiv :
    GlobalEquiv afterFirstReplacement afterSecondReplacement :=
  replaceConstraintEquiv
    afterFirstReplacement
    secondSequentialRepr
    secondSequentialDecomposition

example : GlobalEquiv twoConstraintProblem afterSecondReplacement :=
  firstSequentialEquiv.trans secondSequentialEquiv

end

end MorewTest.ConstraintRepr
