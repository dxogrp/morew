/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic

/-! # Certified selection of feasible representatives -/

namespace MorewTest.Reformulation.Restrict

open Morew
noncomputable section

def symmetric :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      lower_x : 0 ≤ x
      lower_y : 0 ≤ y

def sortingRepair : GlobalImprovement symmetric
    (symmetric.addConstraint (fun point => point.1 ≤ point.2)) where
  map point := ⟨(min point.1.1 point.1.2, max point.1.1 point.1.2),
    ⟨⟨le_min point.2.1 point.2.2, point.2.1.trans (le_max_left _ _)⟩,
      min_le_max⟩⟩
  objective_le point := by
    change min point.1.1 point.1.2 + max point.1.1 point.1.2 ≤ point.1.1 + point.1.2
    rw [min_add_max]

reformulation ordered : symmetric := by
  restrict ordered : x ≤ y using sortingRepair

example : GlobalEquivalence symmetric ordered := ordered.equivalence
example : symmetric.feasible (2, 1) := by constructor <;> norm_num
example : ¬ ordered.feasible (2, 1) := by norm_num [ordered]
example (x y : ℝ) : ordered.objective (x, y) = x + y := rfl
example (x y : ℝ) : ordered.feasible (x, y) ↔
    0 ≤ x ∧ 0 ≤ y ∧ x ≤ y := Iff.rfl

/--
info: problem (x y : ℝ)
  minimize x + y
  subject to
    lower_x : 0 ≤ x
    lower_y : 0 ≤ y
    ordered : x ≤ y
-/
#guard_msgs in
#printp ordered

def maximum :=
  problem (x : ℝ)
    maximize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

def intervalAbsRepair : GlobalImprovement maximum
    (maximum.addConstraint (fun x => 0 ≤ x)) where
  map point := ⟨|point.1|,
    ⟨⟨(by norm_num : (-1 : ℝ) ≤ 0).trans (abs_nonneg _), abs_le.mpr point.2⟩,
      abs_nonneg _⟩⟩
  objective_le point := le_abs_self point.1

reformulation nonnegativeMaximum : maximum := by
  restrict nonnegative : 0 ≤ x using (intervalAbsRepair)

example : GlobalEquivalence maximum nonnegativeMaximum := nonnegativeMaximum.equivalence
example (x : ℝ) : nonnegativeMaximum.feasible x ↔ -1 ≤ x ∧ x ≤ 1 ∧ 0 ≤ x := Iff.rfl
example : ¬ nonnegativeMaximum.feasible (-1) := by norm_num [nonnegativeMaximum]
example : (intervalAbsRepair.map ⟨-1, by constructor <;> norm_num⟩).1 = 1 := by
  norm_num [intervalAbsRepair]
example : (-1 : ℝ) < (intervalAbsRepair.map ⟨-1, by constructor <;> norm_num⟩).1 := by
  norm_num [intervalAbsRepair]

/--
info: problem (x : ℝ)
  maximize x
  subject to
    lower : -1 ≤ x
    upper : x ≤ 1
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp nonnegativeMaximum

def squareLine := problem (x : ℝ) minimize x ^ 2

def squareAbsRepair : GlobalImprovement squareLine
    (squareLine.addConstraint (fun x => 0 ≤ x)) where
  map point := ⟨|point.1|, ⟨True.intro, abs_nonneg _⟩⟩
  objective_le point := by
    change |point.1| ^ 2 ≤ point.1 ^ 2
    rw [sq_abs]

reformulation nonnegativeLine : squareLine := by
  restrict nonnegative : 0 ≤ x using squareAbsRepair

example : GlobalEquivalence squareLine nonnegativeLine := nonnegativeLine.equivalence
example (x : ℝ) : nonnegativeLine.feasible x ↔ 0 ≤ x := Iff.rfl

/--
info: problem (x : ℝ)
  minimize x ^ 2
  subject to
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp nonnegativeLine

-- The new row establishes square coverage. Its transformed tautology is then
-- removed by substitution's independent normalization proof.
reformulation squaredCoordinates : squareLine := by
  restrict nonnegative : 0 ≤ x using squareAbsRepair
  substitute x := u ^ 2
  epigraph t as objective_bound

example : GlobalEquivalence squareLine squaredCoordinates := squaredCoordinates.equivalence
example (u t : ℝ) : squaredCoordinates.objective (u, t) = t := rfl
example (u t : ℝ) : squaredCoordinates.feasible (u, t) ↔ (u ^ 2) ^ 2 ≤ t := Iff.rfl

/--
info: problem (u t : ℝ)
  minimize t
  subject to
    objective_bound : (u ^ 2) ^ 2 ≤ t
-/
#guard_msgs in
#printp squaredCoordinates

def lineSquareCoverage : FeasibleSurjection nonnegativeLine (fun u : ℝ => u ^ 2) where
  preimage point := Real.sqrt point.1
  rightInverse point := Real.sq_sqrt point.2

-- Explicit coverage can name the corresponding canonical checkpoint too.
reformulation squaredExplicitly : squareLine := by
  restrict nonnegative : 0 ≤ x using squareAbsRepair
  substitute x := u ^ 2 using lineSquareCoverage
  epigraph t as objective_bound

example : squaredExplicitly = squaredCoordinates := rfl
example : GlobalEquivalence squareLine squaredExplicitly := squaredExplicitly.equivalence

def nonnegativeSource :=
  problem (x : ℝ)
    minimize (x - 4) ^ 2
    subject to nonnegative : 0 ≤ x

def squareCoverage : FeasibleSurjection nonnegativeSource (fun u : ℝ => u ^ 2) where
  preimage point := Real.sqrt point.1
  rightInverse point := Real.sq_sqrt point.2

def principalRepair := squareCoverage.restrictionImprovement
  (fun u => 0 ≤ u) (fun point => Real.sqrt_nonneg point.1)

reformulation ordinaryCoordinates : nonnegativeSource := by
  substitute x := u ^ 2

-- This helper is about the raw pullback, which is the current semantic source
-- immediately after substitution, even though its displayed domain row is gone.
reformulation principalCoordinates : nonnegativeSource := by
  substitute x := u ^ 2
  restrict branch : 0 ≤ u using principalRepair

example : GlobalEquivalence nonnegativeSource principalCoordinates := principalCoordinates.equivalence
example : ordinaryCoordinates.feasible 2 := True.intro
example : ordinaryCoordinates.feasible (-2) := True.intro
example : ordinaryCoordinates.IsGlobalOptimum ⟨2, True.intro⟩ := by
  intro point
  change ((2 : ℝ) ^ 2 - 4) ^ 2 ≤ (point.1 ^ 2 - 4) ^ 2
  norm_num only [Nat.reducePow, sub_self, zero_pow]
  exact sq_nonneg _
example : ordinaryCoordinates.IsGlobalOptimum ⟨-2, True.intro⟩ := by
  intro point
  change ((-2 : ℝ) ^ 2 - 4) ^ 2 ≤ (point.1 ^ 2 - 4) ^ 2
  norm_num only [neg_sq, Nat.reducePow, sub_self, zero_pow]
  exact sq_nonneg _
example : principalCoordinates.feasible 2 := by norm_num [principalCoordinates]
example : ¬ principalCoordinates.feasible (-2) := by norm_num [principalCoordinates]
example (u : ℝ) (hu : principalCoordinates.feasible u) : Real.sqrt (u ^ 2) = u :=
  Real.sqrt_sq hu

/--
info: problem (u : ℝ)
  minimize (u ^ 2 - 4) ^ 2
  subject to
    branch : 0 ≤ u
-/
#guard_msgs in
#printp principalCoordinates

def middleSource :=
  problem (a x b : ℝ)
    minimize (x - 4) ^ 2 + a ^ 2 + b ^ 2
    subject to nonnegative : 0 ≤ x

def middleCoverage : FeasibleSurjection middleSource
    (fun point : (ℝ × ℝ) × ℝ => ((point.1.1, point.1.2 ^ 2), point.2)) where
  preimage point := ((point.1.1.1, Real.sqrt point.1.1.2), point.1.2)
  rightInverse point := Prod.ext (Prod.ext rfl (Real.sq_sqrt point.2)) rfl

def middleRepair := middleCoverage.restrictionImprovement
  (fun point => 0 ≤ point.1.2) (fun point => Real.sqrt_nonneg point.1.1.2)

-- Both sides of a substituted middle coordinate survive branch selection.
reformulation middleBranch : middleSource := by
  substitute x := u ^ 2 using middleCoverage
  restrict branch : 0 ≤ u using middleRepair

example : GlobalEquivalence middleSource middleBranch := middleBranch.equivalence
example (a u b : ℝ) : middleBranch.objective ((a, u), b) =
    (u ^ 2 - 4) ^ 2 + a ^ 2 + b ^ 2 := rfl
example (a u b : ℝ) : middleBranch.feasible ((a, u), b) ↔ 0 ≤ u := Iff.rfl
example (point : FeasiblePoint middleSource) :
    (middleBranch.equivalence.forward.map point).1.1.1 = point.1.1.1 := rfl
example (point : FeasiblePoint middleSource) :
    (middleBranch.equivalence.forward.map point).1.2 = point.1.2 := rfl
example (point : FeasiblePoint middleBranch) :
    (middleBranch.equivalence.backward.map point).1.1.1 = point.1.1.1 := rfl
example (point : FeasiblePoint middleBranch) :
    (middleBranch.equivalence.backward.map point).1.2 = point.1.2 := rfl

def zeroCapRepair : GlobalImprovement squareLine
    (squareLine.addConstraint (fun x => |x| ≤ 1)) where
  map _ := ⟨0, ⟨True.intro, by norm_num⟩⟩
  objective_le point := by simpa [squareLine, Problem.addConstraint] using sq_nonneg point.1

reformulation capped : squareLine := by
  restrict abs_cap : |x| ≤ 1 using zeroCapRepair

reformulation successive : squareLine := by
  restrict abs_cap : |x| ≤ 1 using zeroCapRepair
  restrict nonnegative : 0 ≤ x using (by
    refine { map := fun _ => ⟨0, ?_⟩, objective_le := ?_ }
    · change |(0 : ℝ)| ≤ 1 ∧ 0 ≤ (0 : ℝ)
      norm_num
    · intro point
      change (0 : ℝ) ^ 2 ≤ point.1 ^ 2
      simpa using sq_nonneg point.1)

reformulation combined : squareLine := by
  restrict representative : |x| ≤ 1 ∧ 0 ≤ x using {
    map := fun _ => ⟨0, ⟨True.intro, by norm_num⟩⟩
    objective_le := fun point => by simpa [squareLine, Problem.addConstraint] using sq_nonneg point.1 }

example : GlobalEquivalence squareLine successive := successive.equivalence
example (x : ℝ) : successive.feasible x ↔ combined.feasible x := Iff.rfl

/--
info: problem (x : ℝ)
  minimize x ^ 2
  subject to
    abs_cap : |x| ≤ 1
    nonnegative : 0 ≤ x
-/
#guard_msgs in
#printp successive

-- Explicit tautologies and conjunctions remain separately labeled rows.
reformulation explicitRows : squareLine := by
  restrict tag : True using {
    map := fun point => ⟨point.1, ⟨point.2, True.intro⟩⟩
    objective_le := fun _ => le_rfl }
  restrict grouped : True ∧ x = x using (by
    exact {
      map := fun point => ⟨point.1, ⟨point.2, True.intro, rfl⟩⟩
      objective_le := fun _ => le_rfl })
  derive duplicate : True using (by intro _ _; trivial)

example (x : ℝ) : explicitRows.feasible x ↔ True ∧ (True ∧ x = x) ∧ True := Iff.rfl

/--
info: problem (x : ℝ)
  minimize x ^ 2
  subject to
    tag : True
    grouped : True ∧ x = x
    duplicate : True
-/
#guard_msgs in
#printp explicitRows

-- A restriction after an epigraph repairs the original coordinate while
-- retaining the auxiliary coordinate and its current feasibility evidence.
reformulation afterEpigraph : squareLine := by
  epigraph t as objective_bound
  restrict zero : x = 0 using (by
    refine { map := fun point => ⟨(0, point.1.2), ?_⟩, objective_le := fun _ => le_rfl }
    change (True ∧ (0 : ℝ) ^ 2 ≤ point.1.2) ∧ (0 : ℝ) = 0
    refine ⟨⟨True.intro, ?_⟩, rfl⟩
    have bound : point.1.1 ^ 2 ≤ point.1.2 := point.2.2
    nlinarith [sq_nonneg point.1.1])

example : GlobalEquivalence squareLine afterEpigraph := afterEpigraph.equivalence
example (x t : ℝ) : afterEpigraph.feasible (x, t) ↔ x ^ 2 ≤ t ∧ x = 0 := Iff.rfl

def shiftedFamily (offset : ℝ) :=
  problem (x : ℝ)
    let shifted := x + offset
    minimize shifted ^ 2

def shiftedRepair (offset : ℝ) : GlobalImprovement (shiftedFamily offset)
    ((shiftedFamily offset).addConstraint (fun x => 0 ≤ x + offset)) where
  map point := ⟨|point.1 + offset| - offset, ⟨True.intro, by
    simp⟩⟩
  objective_le point := by
    simp [shiftedFamily, Problem.addConstraint, sq_abs]

section
variable (offset : ℝ)

reformulation shiftedRestricted : (shiftedFamily offset) := by
  restrict branch : 0 ≤ shifted using shiftedRepair offset

example : GlobalEquivalence (shiftedFamily offset) (shiftedRestricted offset) :=
  shiftedRestricted.equivalence offset
example (x : ℝ) : (shiftedRestricted offset).feasible x ↔ 0 ≤ x + offset := Iff.rfl

/--
info: problem (x : ℝ)
  let shifted := x + offset
  minimize shifted ^ 2
  subject to
    branch : 0 ≤ shifted
-/
#guard_msgs in
#printp shiftedRestricted
end

def dependentDefinitions :=
  problem (x : ℝ)
    let count := 1
    let samples : Fin count → ℝ := fun _ => x
    let sampled : samples 0 = x := rfl
    minimize x ^ 2

reformulation dependentRestricted : dependentDefinitions := by
  restrict branch : 0 ≤ samples 0 using squareAbsRepair

example : GlobalEquivalence dependentDefinitions dependentRestricted := dependentRestricted.equivalence
example (x : ℝ) : dependentRestricted.feasible x ↔ 0 ≤ x := Iff.rfl

section
variable (proofOnly : GlobalImprovement squareLine
  (squareLine.addConstraint (fun x => 0 ≤ x)))

-- Only the certificate depends on this parameter, so its name remains usable.
reformulation proofOnlyParameter : squareLine := by
  restrict nonnegative : 0 ≤ x using proofOnly
  epigraph proofOnly
  substitute x := u

example : GlobalEquivalence squareLine proofOnlyParameter := proofOnlyParameter.equivalence proofOnly
example (u t : ℝ) : proofOnlyParameter.feasible (u, t) ↔ 0 ≤ u ∧ u ^ 2 ≤ t := Iff.rfl
end

section
variable {α : Type*} [AddZeroClass α]

def genericSource := problem (x : α) minimize (0 : ℝ) subject to self : x = x

reformulation anonymousInstance : (genericSource (α := α)) := by
  restrict zero_identity : x + 0 = x using {
    map := fun point => ⟨point.1, ⟨point.2, add_zero _⟩⟩
    objective_le := fun _ => le_rfl }

example : GlobalEquivalence (genericSource (α := α)) (anonymousInstance (α := α)) :=
  anonymousInstance.equivalence
example (x : α) : (anonymousInstance (α := α)).feasible x ↔ x = x ∧ x + 0 = x := Iff.rfl

/--
info: problem (x : α)
  minimize 0
  subject to
    self : x = x
    zero_identity : x + 0 = x
-/
#guard_msgs in
#printp anonymousInstance
end

namespace Hygiene
def branch (x : ℝ) : Prop := 0 ≤ x
macro "capturedBranch " x:term : term => `(branch $x)

reformulation target : squareLine := by
  restrict branch : capturedBranch x using squareAbsRepair

-- A constraint may share its spelling with a decision or a global declaration.
reformulation binderLabel : squareLine := by
  restrict x : 0 ≤ x using squareAbsRepair

example (x : ℝ) : target.feasible x ↔ branch x := Iff.rfl
example (x : ℝ) : binderLabel.feasible x ↔ 0 ≤ x := Iff.rfl
end Hygiene

end
end MorewTest.Reformulation.Restrict
