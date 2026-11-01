/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew
import Morew.Elab.Substitution.Rules

/-! # Theorem-backed coordinate substitution through the public DSL -/

namespace MorewTest.Reformulation.SubstitutionRules

open Morew
noncomputable section

def scalar := problem (x : ℝ) minimize x

reformulation renamed : scalar := by substitute x := u
reformulation negated : scalar := by substitute x := -u
reformulation multipliedLeft : scalar := by substitute x := 2 * u
reformulation multipliedRight : scalar := by substitute x := u * (-3)
reformulation shiftedRight : scalar := by substitute x := u + 2
reformulation shiftedLeft : scalar := by substitute x := 2 + u
reformulation subtractedRight : scalar := by substitute x := u - 2
reformulation subtractedLeft : scalar := by substitute x := 2 - u
reformulation affine : scalar := by substitute x := (-2) * u + 3

example (u : ℝ) : renamed.objective u = u := rfl
example (u : ℝ) : negated.objective u = -u := rfl
example (u : ℝ) : multipliedLeft.objective u = 2 * u := rfl
example (u : ℝ) : multipliedRight.objective u = u * (-3) := rfl
example (u : ℝ) : shiftedRight.objective u = u + 2 := rfl
example (u : ℝ) : shiftedLeft.objective u = 2 + u := rfl
example (u : ℝ) : subtractedRight.objective u = u - 2 := rfl
example (u : ℝ) : subtractedLeft.objective u = 2 - u := rfl
example (u : ℝ) : affine.objective u = (-2) * u + 3 := rfl
example : GlobalEquivalence scalar affine := affine.equivalence

def natural := problem (x : ℕ) minimize x
reformulation naturalRenamed : natural := by substitute x := u
example : GlobalEquivalence natural naturalRenamed := naturalRenamed.equivalence

def nonnegative :=
  problem (x : ℝ)
    minimize x
    subject to
      explicit_true : True
      domain : 0 ≤ x
      upper : x ≤ 4

reformulation squared : nonnegative := by substitute x := u ^ 2
reformulation squaredNamed : nonnegative := by
  substitute x := u ^ 2 via Morew.Substitution.square
reformulation squaredApplied : nonnegative := by
  substitute x := u ^ 2 via (Morew.Substitution.square (R := Unit))

example (u : ℝ) : squared.objective u = u ^ 2 := rfl
example (u : ℝ) : squared.feasible u ↔ True ∧ u ^ 2 ≤ 4 := Iff.rfl
example : GlobalEquivalence nonnegative squared := squared.equivalence
example : GlobalEquivalence nonnegative squaredNamed := squaredNamed.equivalence
example : GlobalEquivalence nonnegative squaredApplied := squaredApplied.equivalence

/--
info: problem (u : ℝ)
  minimize u ^ 2
  subject to
    explicit_true : True
    upper : u ^ 2 ≤ 4
-/
#guard_msgs in
#printp squared
example : squared.feasible 0 := ⟨True.intro, by norm_num⟩

def zeroSource :=
  problem (x : ℝ)
    maximize x
    subject to
      domain : 0 ≤ x
      zero : x = 0

reformulation zeroSquare : zeroSource := by substitute x := u ^ 2
example : zeroSquare.feasible 0 := by norm_num [zeroSquare]
example : GlobalEquivalence zeroSource zeroSquare := zeroSquare.equivalence

def shared :=
  problem (x : ℝ)
    minimize Real.log x
    subject to shared_domain : let y := x; True ∧ (0 < y ∧ y ≤ 4)

reformulation sharedExponential : shared := by substitute x := Real.exp u
example : GlobalEquivalence shared sharedExponential := sharedExponential.equivalence

def marginSource (epsilon : ℝ) :=
  problem (x : ℝ)
    minimize Real.log x
    subject to lower : x ≥ epsilon

section
variable (epsilon : ℝ) (positive : 0 < epsilon)
reformulation marginExponential : (marginSource epsilon) := by
  substitute x := Real.exp u
reformulation marginSquare : (marginSource epsilon) := by
  substitute x := u ^ 2
example (u : ℝ) : (marginExponential epsilon).feasible u ↔ Real.exp u ≥ epsilon :=
  Iff.rfl
example : GlobalEquivalence (marginSource epsilon) (marginSquare epsilon) :=
  marginSquare.equivalence epsilon positive
end

def MarginEvidence (epsilon : ℝ) : Prop := True ∧ 0 < epsilon

section
variable (epsilon : ℝ) (positive : MarginEvidence epsilon)

reformulation aliasedMargin : (marginSource epsilon) := by
  substitute x := Real.exp u

example : GlobalEquivalence (marginSource epsilon) (aliasedMargin epsilon) :=
  aliasedMargin.equivalence epsilon positive
end

def positiveMargin :=
  problem (x : ℝ)
    minimize Real.log x
    subject to lower : 1 ≤ x

reformulation retainedMargin : positiveMargin := by substitute x := Real.exp u
example (u : ℝ) : retainedMargin.feasible u ↔ 1 ≤ Real.exp u := Iff.rfl

def dependentSlope :=
  problem (a x : ℝ)
    minimize x
    subject to slope : a ≠ 0

reformulation dependentLeft : dependentSlope := by substitute x := a * u
reformulation dependentRight : dependentSlope := by substitute x := u * a
reformulation dependentShift : dependentSlope := by substitute x := u + a
reformulation dependentAffine : dependentSlope := by substitute x := a * u + a
reformulation dependentSelected : dependentSlope := by
  substitute x := a * u + a via
    (Morew.Substitution.affine (fun a : ℝ => a) (fun a : ℝ => a))

example (a u : ℝ) : dependentAffine.objective (a, u) = a * u + a := rfl
example (a u : ℝ) : dependentAffine.feasible (a, u) ↔ a ≠ 0 := Iff.rfl
example : GlobalEquivalence dependentSlope dependentSelected := dependentSelected.equivalence

def reverseDisequality :=
  problem (a x : ℝ)
    minimize x
    subject to slope : 0 ≠ a

reformulation reverseDisequalityTarget : reverseDisequality := by
  substitute x := a * u

example : GlobalEquivalence reverseDisequality reverseDisequalityTarget :=
  reverseDisequalityTarget.equivalence

/--
info: problem (a u : ℝ)
  minimize a * u + a
  subject to
    slope : a ≠ 0
-/
#guard_msgs in
#printp dependentAffine

def positiveSlope :=
  problem (a x : ℝ)
    minimize x
    subject to slope : 0 < a
reformulation positiveDependent : positiveSlope := by substitute x := a * u

def negativeSlope :=
  problem (a x : ℝ)
    minimize x
    subject to slope : a < 0
reformulation negativeDependent : negativeSlope := by substitute x := a * u

example : GlobalEquivalence positiveSlope positiveDependent := positiveDependent.equivalence
example : GlobalEquivalence negativeSlope negativeDependent := negativeDependent.equivalence

-- A sufficient coverage range is not an assertion about all forward images.
-- Renaming with this descriptor must retain the original nonnegativity row.
def restrictedIdentity {R : Type*} :
    CoordinateParameterization (fun (_ : R) (u : ℝ) => u) where
  range _ x := 0 ≤ x
  preimage _ x := x.1
  rightInverse _ _ := rfl

reformulation restrictedRenaming : nonnegative := by
  substitute x := u via restrictedIdentity
example (u : ℝ) : restrictedRenaming.feasible u ↔ True ∧ 0 ≤ u ∧ u ≤ 4 := Iff.rfl

-- Existing whole-problem certificates bypass descriptor discovery.
def manualCoverage : FeasibleSurjection scalar (fun u : ℝ => 2 * (u + 1)) where
  preimage x := x.1 / 2 - 1
  rightInverse x := by ring
reformulation manual : scalar := by
  substitute x := 2 * (u + 1) using manualCoverage
example : GlobalEquivalence scalar manual := manual.equivalence

def squareRootSource :=
  problem (x : ℝ)
    minimize Real.sqrt x
    subject to domain : 0 ≤ x
reformulation squareRootTarget : squareRootSource := by substitute x := u ^ 2
example (u : ℝ) : squareRootTarget.objective u = Real.sqrt (u ^ 2) := rfl
example : squareRootTarget.objective (-2) = 2 := by
  change Real.sqrt ((-2 : ℝ) ^ 2) = 2
  rw [Real.sqrt_sq_eq_abs]
  norm_num

namespace MiddleCoordinate

def minimum :=
  problem (a x b : ℝ)
    minimize a + x + b
    subject to domain : 0 ≤ x

reformulation target : minimum := by
  epigraph t as objective_bound
  substitute x := u ^ 2

example (a u b t : ℝ) : target.feasible (((a, u), b), t) ↔ a + u ^ 2 + b ≤ t := Iff.rfl
example (point : FeasiblePoint minimum) :
    let mapped := target.equivalence.forward.map point
    mapped.1.1.1.1 = point.1.1.1 ∧
      mapped.1.1.1.2 = Real.sqrt point.1.1.2 ∧ mapped.1.1.2 = point.1.2 := by
  constructor
  · rfl
  constructor <;> rfl
example (point : FeasiblePoint target) :
    let mapped := target.equivalence.backward.map point
    mapped.1.1.1 = point.1.1.1.1 ∧
      mapped.1.1.2 = point.1.1.1.2 ^ 2 ∧ mapped.1.2 = point.1.1.2 := by
  constructor
  · rfl
  constructor <;> rfl

def maximum :=
  problem (a x b : ℝ)
    maximize a + x + b
    subject to domain : 0 ≤ x

reformulation maximumTarget : maximum := by
  hypograph t as objective_bound
  substitute x := u ^ 2
example : GlobalEquivalence maximum maximumTarget := maximumTarget.equivalence
example (a u b t : ℝ) : maximumTarget.feasible (((a, u), b), t) ↔ t ≤ a + u ^ 2 + b :=
  Iff.rfl

end MiddleCoordinate

/-- A downstream function with a named head discoverable after import. -/
def shiftedSquare (u : ℝ) : ℝ := u ^ 2 + 1

@[morew_substitute]
def shiftedSquareRule {R : Type*} :
    CoordinateParameterization (fun (_ : R) (u : ℝ) => shiftedSquare u) where
  range _ x := 1 ≤ x
  preimage _ x := Real.sqrt (x.1 - 1)
  rightInverse _ x := by
    rw [shiftedSquare, Real.sq_sqrt (sub_nonneg.mpr x.2), sub_add_cancel]

-- Continued conic and NLP certification use the resulting semantic problem.
reformulation squaredConic : nonnegative := by
  substitute x := u ^ 2
  epigraph t
  conic
example : IsConic squaredConic := squaredConic.isConic
example : GlobalEquivalence nonnegative squaredConic := squaredConic.equivalence

reformulation squaredNLP : nonnegative := by
  substitute x := u ^ 2
  nlp
example : IsSmoothNLP squaredNLP := squaredNLP.isSmoothNLP

end
end MorewTest.Reformulation.SubstitutionRules
