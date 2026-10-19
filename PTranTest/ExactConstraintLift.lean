import PTran.Transform
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Real.Basic

/-!
# Tests for exact auxiliary-variable constraint lifts

These tests exercise the semantic API directly.  In particular, they do not
depend on the reformulation command or its presentation metadata.
-/

namespace PTranTest.ExactConstraintLift

open PTran

noncomputable section

/-! A pointwise equivalence can be packaged as a lift with `Unit` auxiliary
data. -/

def zeroSymmetryLift : ExactConstraintLift (fun x : ℤ => x = 0) :=
  ExactConstraintLift.ofIff
    (fun x : ℤ => 0 = x)
    fun x =>
      ⟨fun h : x = 0 => h.symm, fun h : 0 = x => h.symm⟩

example : zeroSymmetryLift.Auxiliary = Unit := rfl

example (x : ℤ) :
    zeroSymmetryLift.target x () ↔ 0 = x :=
  Iff.rfl

/-! A one-auxiliary representation of the epigraph of the square function. -/

def squareEpigraphRepresentation :
    EpigraphRepresentation (fun x : ℤ => x ^ 2) where
  Auxiliary := ℤ
  target x t a := a = x ^ 2 ∧ a ≤ t
  source_iff_exists x t := by
    constructor
    · intro h
      exact ⟨x ^ 2, rfl, h⟩
    · rintro ⟨a, rfl, h⟩
      exact h

def squareEpigraphLift :
    ExactConstraintLift (fun point : ℤ × ℤ => point.1 ^ 2 ≤ point.2) :=
  squareEpigraphRepresentation.toExactConstraintLift Prod.fst Prod.snd

def squareBoundProblem : Problem (ℤ × ℤ) ℤ where
  objective point := point.1 + point.2
  feasible point := point.1 ≤ 10 ∧ point.1 ^ 2 ≤ point.2

def squareBoundDecomposition :
    ConstraintDecomposition squareBoundProblem
      (fun point : ℤ × ℤ => point.1 ^ 2 ≤ point.2) where
  remainder point := point.1 ≤ 10
  feasible_iff _ := Iff.rfl

def liftedSquareBoundProblem : Problem ((ℤ × ℤ) × ℤ) ℤ :=
  squareBoundProblem.liftConstraint
    squareEpigraphLift
    (decomposition := squareBoundDecomposition)

def squareBoundEquivalence :
    GlobalEquivalence squareBoundProblem liftedSquareBoundProblem :=
  exactConstraintLiftEquivalence
    squareBoundProblem
    squareEpigraphLift
    squareBoundDecomposition

def squareBoundPoint : FeasiblePoint squareBoundProblem :=
  ⟨(2, 4), by
    change (2 : ℤ) ≤ 10 ∧ (2 : ℤ) ^ 2 ≤ 4
    decide⟩

example :
    (squareBoundEquivalence.forward.map squareBoundPoint).1.1 =
      squareBoundPoint.1 :=
  rfl

example :
    liftedSquareBoundProblem.objective
        (squareBoundEquivalence.forward.map squareBoundPoint).1 =
      squareBoundProblem.objective squareBoundPoint.1 :=
  rfl

example (point : FeasiblePoint liftedSquareBoundProblem) :
    (squareBoundEquivalence.backward.map point).1 = point.1.1 :=
  rfl

example (point : FeasiblePoint liftedSquareBoundProblem) :
    squareBoundProblem.objective
        (squareBoundEquivalence.backward.map point).1 =
      liftedSquareBoundProblem.objective point.1 :=
  rfl

/-! Graph conversion works for both orientations of the graph equation, and
hypograph conversion preserves its inequality orientation. -/

def successorGraphRepresentation :
    GraphRepresentation (fun x : ℤ => x + 1) where
  Auxiliary := Unit
  target x y _ := y = x + 1
  source_iff_exists x y := by
    constructor
    · intro h
      exact ⟨(), h⟩
    · rintro ⟨_, h⟩
      exact h

example : ExactConstraintLift
    (fun point : ℤ × ℤ => point.2 = point.1 + 1) :=
  successorGraphRepresentation.toExactConstraintLift Prod.fst Prod.snd

example : ExactConstraintLift
    (fun point : ℤ × ℤ => point.1 + 1 = point.2) :=
  successorGraphRepresentation.toExactConstraintLiftSymm Prod.fst Prod.snd

example : ExactConstraintLift
    (fun point : ℤ => point = (point - 1) + 1) :=
  successorGraphRepresentation.toExactConstraintLift (fun point => point - 1) id

def squareHypographRepresentation :
    HypographRepresentation (fun x : ℤ => x ^ 2) where
  Auxiliary := Unit
  target x t _ := t ≤ x ^ 2
  source_iff_exists x t := by
    constructor
    · intro h
      exact ⟨(), h⟩
    · rintro ⟨_, h⟩
      exact h

example : ExactConstraintLift
    (fun point : ℤ × ℤ => point.2 ≤ point.1 ^ 2) :=
  squareHypographRepresentation.toExactConstraintLift Prod.fst Prod.snd

/-! Exactness requires existence, not a unique auxiliary witness. -/

def nonuniqueProductLift : ExactConstraintLift (fun x : ℤ => x = 0) where
  Auxiliary := ℤ × Bool
  target x _ := x = 0
  source_iff_exists x := by
    constructor
    · intro h
      exact ⟨(0, false), h⟩
    · rintro ⟨_, h⟩
      exact h

example :
    nonuniqueProductLift.target 0 (0, false) ∧
      nonuniqueProductLift.target 0 (1, true) ∧
      ((0 : ℤ), false) ≠ (1, true) := by
  simp [nonuniqueProductLift]

/-! Infeasibility is transported in both directions by the equivalence. -/

def impossibleLift : ExactConstraintLift (fun _ : ℤ => False) :=
  ExactConstraintLift.ofIff (fun _ : ℤ => False) fun _ => Iff.rfl

def impossibleProblem : Problem ℤ ℤ where
  objective x := x
  feasible _ := True ∧ False

def impossibleDecomposition :
    ConstraintDecomposition impossibleProblem (fun _ : ℤ => False) where
  remainder _ := True
  feasible_iff _ := Iff.rfl

def liftedImpossibleProblem : Problem (ℤ × Unit) ℤ :=
  impossibleProblem.liftConstraint
    impossibleLift
    impossibleDecomposition

def impossibleEquivalence :
    GlobalEquivalence impossibleProblem liftedImpossibleProblem :=
  exactConstraintLiftEquivalence
    impossibleProblem
    impossibleLift
    impossibleDecomposition

example :
    impossibleProblem.HasFeasiblePoint ↔
      liftedImpossibleProblem.HasFeasiblePoint :=
  impossibleEquivalence.hasFeasiblePoint_iff

example : ¬ liftedImpossibleProblem.HasFeasiblePoint := by
  intro h
  have sourceHasPoint : impossibleProblem.HasFeasiblePoint :=
    impossibleEquivalence.hasFeasiblePoint_iff.mpr h
  obtain ⟨point⟩ := sourceHasPoint
  exact point.2.2

/-! No convexity premise is needed, including for a disconnected feasible
set such as `x² = 1`. -/

def nonconvexProblem : Problem ℝ ℝ where
  objective x := x
  feasible x := True ∧ x ^ 2 = 1

def nonconvexLift : ExactConstraintLift (fun x : ℝ => x ^ 2 = 1) :=
  ExactConstraintLift.ofIff
    (fun x : ℝ => x * x = 1)
    fun x => by
      simp only [pow_two]

def nonconvexDecomposition :
    ConstraintDecomposition nonconvexProblem
      (fun x : ℝ => x ^ 2 = 1) where
  remainder _ := True
  feasible_iff _ := Iff.rfl

def liftedNonconvexProblem :=
  nonconvexProblem.liftConstraint
    nonconvexLift
    nonconvexDecomposition

example : GlobalEquivalence nonconvexProblem liftedNonconvexProblem :=
  exactConstraintLiftEquivalence
    nonconvexProblem
    nonconvexLift
    nonconvexDecomposition

/-! Independently certified lifts compose through transitivity. -/

def twoConstraintProblem : Problem ℤ ℤ where
  objective x := x
  feasible x := x ≤ 0 ∧ x = 0

def firstSequentialLift : ExactConstraintLift (fun x : ℤ => x = 0) :=
  ExactConstraintLift.ofIff
    (fun x : ℤ => 0 = x)
    fun x =>
      ⟨fun h : x = 0 => h.symm, fun h : 0 = x => h.symm⟩

def firstSequentialDecomposition :
    ConstraintDecomposition twoConstraintProblem
      (fun x : ℤ => x = 0) where
  remainder x := x ≤ 0
  feasible_iff _ := Iff.rfl

def afterFirstLift : Problem (ℤ × Unit) ℤ :=
  twoConstraintProblem.liftConstraint
    firstSequentialLift
    firstSequentialDecomposition

def firstSequentialEquivalence :
    GlobalEquivalence twoConstraintProblem afterFirstLift :=
  exactConstraintLiftEquivalence
    twoConstraintProblem
    firstSequentialLift
    firstSequentialDecomposition

def secondSequentialLift :
    ExactConstraintLift (fun point : ℤ × Unit => 0 = point.1) :=
  ExactConstraintLift.ofIff
    (fun point : ℤ × Unit => point.1 = 0)
    fun point =>
      ⟨fun h : 0 = point.1 => h.symm, fun h : point.1 = 0 => h.symm⟩

def secondSequentialDecomposition :
    ConstraintDecomposition afterFirstLift
      (fun point : ℤ × Unit => 0 = point.1) where
  remainder point := point.1 ≤ 0
  feasible_iff _ := Iff.rfl

def afterSecondLift : Problem ((ℤ × Unit) × Unit) ℤ :=
  afterFirstLift.liftConstraint
    secondSequentialLift
    secondSequentialDecomposition

def secondSequentialEquivalence :
    GlobalEquivalence afterFirstLift afterSecondLift :=
  exactConstraintLiftEquivalence
    afterFirstLift
    secondSequentialLift
    secondSequentialDecomposition

example : GlobalEquivalence twoConstraintProblem afterSecondLift :=
  firstSequentialEquivalence.trans secondSequentialEquivalence

end

end PTranTest.ExactConstraintLift
