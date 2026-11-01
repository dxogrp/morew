/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew

/-! # Constraint labels are editable presentation, independent of row identity -/

namespace MorewTest.Reformulation.Rename

open Morew
noncomputable section

def orderedSource :=
  problem (x : ℝ)
    let shifted := x + 1
    minimize shifted
    subject to
      first : 0 ≤ x
      middle : x ≤ 3
      last : shifted ≤ 5

reformulation ordered : orderedSource := by
  rename constraint first to lower
  rename constraint middle to bounds.upper
  rename constraint last to shifted
  rename constraint bounds.upper to bounds.upper

reformulation sameName : orderedSource := by
  rename constraint middle to middle

example : ordered = orderedSource := rfl
example : sameName = orderedSource := rfl
example : GlobalEquivalence orderedSource ordered := ordered.equivalence

/--
info: problem (x : ℝ)
  let shifted := x + 1
  minimize shifted
  subject to
    lower : 0 ≤ x
    bounds.upper : x ≤ 3
    shifted : shifted ≤ 5
-/
#guard_msgs in
#printp ordered

-- The vacated name is available immediately, and labels may match binders.
reformulation reused : orderedSource := by
  rename constraint first to x
  derive first : x ≤ 3 using (by intro point hp; exact hp.2.1)
  rename constraint first to copied

example (x : ℝ) : reused.feasible x ↔
    0 ≤ x ∧ x ≤ 3 ∧ x + 1 ≤ 5 ∧ x ≤ 3 := Iff.rfl

def trueRepair {X V : Type*} [Preorder V] (p : Problem X V) :
    GlobalImprovement p (p.addConstraint (fun _ => True)) where
  map point := ⟨point.1, point.2, True.intro⟩
  objective_le _ := le_rfl

reformulation restricted : orderedSource := by
  rename constraint first to lower
  restrict first : True using trueRepair orderedSource
  rename constraint first to tag
  substitute x := u

example (u : ℝ) : restricted.feasible u ↔
    0 ≤ u ∧ u ≤ 3 ∧ u + 1 ≤ 5 ∧ True := Iff.rfl

def maximum :=
  problem (x : ℝ)
    maximize x
    subject to lower : 0 ≤ x

reformulation maximumBound : maximum := by
  rename constraint lower to domain
  hypograph t as bound
  rename constraint bound to lower_bound
  substitute x := u

example (u t : ℝ) : maximumBound.objective (u, t) = t := rfl
example (u t : ℝ) : maximumBound.feasible (u, t) ↔ 0 ≤ u ∧ t ≤ u := Iff.rfl
example : GlobalEquivalence maximum maximumBound := maximumBound.equivalence

def Positive (x : ℝ) : Prop := 0 < x

def positiveSource :=
  problem (x y : ℝ)
    minimize Real.log x + Real.log y
    subject to
      first : x ≤ 3
      second : Positive x
      third : Positive y

-- `second` has disappeared, but its private identity must never be assigned to
-- the live row that later takes its label. A second removal also shifts slots.
reformulation removedLabelReused : positiveSource := by
  substitute x := Real.exp u
  rename constraint first to second
  rename constraint third to remaining_positive
  substitute y := Real.exp v
  epigraph t as third

example (u v t : ℝ) : removedLabelReused.feasible ((u, v), t) ↔
    Real.exp u ≤ 3 ∧ u + v ≤ t := Iff.rfl
example : GlobalEquivalence positiveSource removedLabelReused :=
  removedLabelReused.equivalence

reformulation renamedAliasRemoved : positiveSource := by
  rename constraint second to domain_x
  rename constraint third to domain_y
  substitute x := Real.exp u
  substitute y := Real.exp v
  epigraph t as domain_x
  rename constraint domain_x to objective_bound

example : renamedAliasRemoved = removedLabelReused := rfl

def leadingPositive :=
  problem (x y : ℝ)
    minimize Real.log x + Real.log y
    subject to
      first : Positive x
      middle : x ≤ 3
      last : Positive y

reformulation shiftedIdentities : leadingPositive := by
  substitute x := Real.exp u
  rename constraint middle to first
  rename constraint last to final_domain
  substitute y := Real.exp v
  epigraph t as final_domain

example : shiftedIdentities = removedLabelReused := rfl

def groupedSource :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      tag : True
      grouped : x ≤ 3 ∧ x ≤ 4
      positive : Positive x

reformulation grouped : groupedSource := by
  rename constraint tag to retained
  rename constraint grouped to bounds
  rename constraint positive to domain
  substitute x := Real.exp u
  epigraph t as objective_bound
  rename constraint objective_bound to bound
  substitute u := v

example (v t : ℝ) : grouped.feasible (v, t) ↔
    True ∧ (Real.exp v ≤ 3 ∧ Real.exp v ≤ 4) ∧ v ≤ t := Iff.rfl

def zero := problem (_x : ℝ) minimize (0 : ℝ)

-- Bounds created after the source checkpoint also have removable identities.
reformulation zeroBoundRemoved : zero := by
  epigraph t as bound
  substitute t := u ^ 2

reformulation renamedZeroBoundRemoved : zero := by
  epigraph t as bound
  rename constraint bound to positive
  substitute t := u ^ 2

reformulation zeroContinued : zero := by
  epigraph t as bound
  rename constraint bound to positive
  substitute t := u ^ 2
  epigraph s as positive
  rename constraint positive to square_bound

example : zeroBoundRemoved = renamedZeroBoundRemoved := rfl
example : GlobalEquivalence zero zeroBoundRemoved := zeroBoundRemoved.equivalence
example : GlobalEquivalence zero renamedZeroBoundRemoved := renamedZeroBoundRemoved.equivalence
example (x u : ℝ) : zeroBoundRemoved.objective (x, u) = u ^ 2 := rfl
example (x u : ℝ) : zeroBoundRemoved.feasible (x, u) ↔ True := Iff.rfl
example (x u s : ℝ) : zeroContinued.feasible ((x, u), s) ↔ u ^ 2 ≤ s := Iff.rfl

def taggedZero := problem (_x : ℝ) minimize (0 : ℝ) subject to retained : True

def squareBoundCoverage :
    FeasibleSurjection taggedZero.epigraph
      (fun point : ℝ × ℝ => (point.1, point.2 ^ 2)) where
  preimage point := (point.1.1, Real.sqrt point.1.2)
  rightInverse point := Prod.ext rfl (Real.sq_sqrt point.2.2)

def squareBoundRepair := squareBoundCoverage.restrictionImprovement
  (fun point => 0 ≤ point.2) (fun point => Real.sqrt_nonneg point.1.2)

-- Explicit certificates still target the natural epigraph and raw pullback,
-- even though checkpoints remove their tautological rows from presentation.
reformulation principalBound : taggedZero := by
  epigraph t as bound
  rename constraint bound to domain
  substitute t := u ^ 2 using squareBoundCoverage
  rename constraint retained to kept
  restrict branch : 0 ≤ u using squareBoundRepair
  rename constraint branch to nonnegative

example (x u : ℝ) : principalBound.feasible (x, u) ↔ True ∧ 0 ≤ u := Iff.rfl
example : GlobalEquivalence taggedZero principalBound := principalBound.equivalence

def absoluteSource :=
  problem (x : ℝ)
    minimize x
    subject to
      before : -5 ≤ x
      magnitude : |x| ≤ 3
      after : x ≤ 5

def upperLift : ExactConstraintLift (fun x : ℝ => x ≤ 3) :=
  .ofIff (fun x => x ≤ 3) (fun _ => Iff.rfl)

-- Current labels select rewrites, and generated families use that current
-- spelling. Individual generated rows can then be renamed and selected again.
reformulation conicRows : absoluteSource := by
  rename constraint magnitude to cap
  conic at cap
  rename constraint cap_conic_1 to upper
  conic at upper using upperLift
  rename constraint upper_conic_1 to upper

reformulation nlpRows : absoluteSource := by
  rename constraint magnitude to cap
  nlp at cap
  rename constraint cap_nlp_1 to upper
  nlp at upper using upperLift
  rename constraint upper_nlp_1 to upper

example (x : ℝ) : conicRows.feasible x ↔
    -5 ≤ x ∧ x ≤ 3 ∧ -x ≤ 3 ∧ x ≤ 5 := Iff.rfl
example : nlpRows = conicRows := rfl
example : GlobalEquivalence absoluteSource conicRows := conicRows.equivalence
example : GlobalEquivalence absoluteSource nlpRows := nlpRows.equivalence

reformulation conicTerminal : absoluteSource := by
  rename constraint magnitude to cap
  conic

reformulation nlpTerminal : absoluteSource := by
  rename constraint magnitude to cap
  nlp

example : IsConic conicTerminal := conicTerminal.isConic
example : IsSmoothNLP nlpTerminal := nlpTerminal.isSmoothNLP

reformulation occurrenceRows : absoluteSource := by
  rename constraint magnitude to budget
  epigraph a at (|x|) in budget as magnitude
  rename constraint magnitude to lifted
  conic at lifted
  rename constraint lifted_conic_1 to positive_side

example (x a : ℝ) : occurrenceRows.feasible (x, a) ↔
    -5 ≤ x ∧ a ≤ 3 ∧ x ≤ 5 ∧ x ≤ a ∧ -x ≤ a := Iff.rfl

def lowerSource :=
  problem (x : ℝ)
    maximize x
    subject to lower : 1 ≤ x ^ 2

reformulation lowerOccurrence : lowerSource := by
  rename constraint lower to floor
  hypograph t at (x ^ 2) in floor as bound
  rename constraint bound to square_bound

example (x t : ℝ) : lowerOccurrence.feasible (x, t) ↔ 1 ≤ t ∧ t ≤ x ^ 2 := Iff.rfl

def vectorSource :=
  problem (v : Fin 2 → ℝ)
    minimize ∑ i, v i
    subject to bounds : 0 ≤ v ∧ v ≤ (fun _ => 3)

reformulation vectorRenamed : vectorSource := by
  rename constraint bounds to coordinate_bounds

reformulation vectorConic : vectorSource := by
  rename constraint bounds to coordinate_bounds
  conic

example : vectorRenamed = vectorSource := rfl
example (v : Fin 2 → ℝ) : vectorRenamed.feasible v ↔
    0 ≤ v ∧ v ≤ (fun _ => 3) := Iff.rfl
example : IsConic vectorConic := vectorConic.isConic
example : GlobalEquivalence vectorSource vectorConic := vectorConic.equivalence

section
variable (offset : ℝ)

def family :=
  problem (x : ℝ)
    let shifted := x + offset
    minimize shifted ^ 2
    subject to original : 0 ≤ shifted

reformulation renamedFamily : (family offset) := by
  rename constraint original to offset
  rename constraint offset to domain

example : renamedFamily offset = family offset := rfl
end

namespace Instances

set_option linter.overlappingInstances false

class Parameter where
  value : ℝ

variable [first : Parameter] [second : Parameter]

def source :=
  problem (x : ℝ)
    let left := @Parameter.value first
    let right := @Parameter.value second
    minimize left + x
    subject to bounds : right ≤ x ∧ x ≤ left

reformulation target : (@source first second) := by
  rename constraint bounds to interval

example : @target first second = @source first second := rfl

reformulation bounded : (@source first second) := by
  epigraph t as objective_bound
  rename constraint bounds to interval
  rename constraint objective_bound to bound
  substitute x := u

example (u t : ℝ) : (@bounded first second).feasible (u, t) ↔
    (@Parameter.value second ≤ u ∧ u ≤ @Parameter.value first) ∧
      @Parameter.value first + u ≤ t := Iff.rfl
end Instances

namespace Hygiene

def cap (x : ℝ) : Prop := x ≤ 3

def source :=
  problem (x : ℝ)
    minimize x
    subject to cap : cap x

reformulation target : source := by
  rename constraint cap to bound

example (x : ℝ) : target.feasible x ↔ cap x := Iff.rfl
end Hygiene

run_cmd do
  for (name, expected) in #[
      (``ordered, #[`lower, `bounds.upper, `shifted]),
      (``sameName, #[`first, `middle, `last]),
      (``reused, #[`x, `middle, `last, `copied]),
      (``restricted, #[`lower, `middle, `last, `tag]),
      (``maximumBound, #[`domain, `lower_bound]),
      (``removedLabelReused, #[`second, `third]),
      (``renamedAliasRemoved, #[`first, `objective_bound]),
      (``shiftedIdentities, #[`first, `final_domain]),
      (``grouped, #[`retained, `bounds, `bound]),
      (``zeroBoundRemoved, #[]),
      (``renamedZeroBoundRemoved, #[]),
      (``zeroContinued, #[`square_bound]),
      (``principalBound, #[`kept, `nonnegative]),
      (``conicRows, #[`before, `upper, `cap_conic_2, `after]),
      (``nlpRows, #[`before, `upper, `cap_nlp_2, `after]),
      (``occurrenceRows, #[`before, `budget, `after, `positive_side, `lifted_conic_2]),
      (``lowerOccurrence, #[`floor, `square_bound]),
      (``vectorRenamed, #[`coordinate_bounds]),
      (``vectorConic, #[`coordinate_bounds]),
      (``renamedFamily, #[`domain]),
      (``Instances.target, #[`interval])] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing renamed presentation for {name}"
    let actual := view.constraints.map (·.name.eraseMacroScopes)
    unless actual == expected do
      Lean.throwError "unexpected labels for {name}: {actual}; expected {expected}"

end
end MorewTest.Reformulation.Rename
