/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic

/-! # Visible, theorem-backed constraints over the current problem -/

namespace MorewTest.Reformulation.Derive

open Morew
noncomputable section

def free := problem (x : ℝ) minimize x

reformulation oneRow : free := by
  derive square_nonnegative : 0 ≤ x ^ 2 using (by
    intro point _
    exact sq_nonneg point)

example : GlobalEquivalence free oneRow := oneRow.equivalence
example (x : ℝ) : oneRow.objective x = x := rfl
example (x : ℝ) : oneRow.feasible x ↔ 0 ≤ x ^ 2 := Iff.rfl

/--
info: problem (x : ℝ)
  minimize x
  subject to
    square_nonnegative : 0 ≤ x ^ 2
-/
#guard_msgs in
#printp oneRow

-- Derivation adds actual rows, even when their predicates are tautologies or
-- duplicates. A displayed conjunction remains one labeled constraint.
reformulation successive : free := by
  derive first : True using (by intro _ _; trivial)
  derive grouped : True ∧ x = x using (by intro _ _; exact ⟨True.intro, rfl⟩)
  derive second : True using (by intro _ _; trivial)

example (x : ℝ) : successive.feasible x ↔ True ∧ (True ∧ x = x) ∧ True := Iff.rfl
example : GlobalEquivalence free successive := successive.equivalence

/--
info: problem (x : ℝ)
  minimize x
  subject to
    first : True
    grouped : True ∧ x = x
    second : True
-/
#guard_msgs in
#printp successive

-- Constraint labels and decision binders have independent namespaces.
reformulation binderLabel : free := by
  derive x : x = x using (by intro _ _; rfl)

example (x : ℝ) : binderLabel.feasible x ↔ x = x := Iff.rfl

/--
info: problem (x : ℝ)
  minimize x
  subject to
    x : x = x
-/
#guard_msgs in
#printp binderLabel

def transitiveSource :=
  problem (y x : ℝ)
    maximize Real.log x
    subject to
      lower : 1 ≤ y
      ordered : y ≤ x

theorem marginOfFeasible :
    ∀ point, transitiveSource.feasible point → 1 ≤ point.2 := by
  intro point hp
  exact le_trans hp.1 hp.2

reformulation withMargin : transitiveSource := by
  derive margin : 1 ≤ x using marginOfFeasible

example (y x : ℝ) : withMargin.feasible (y, x) ↔
    1 ≤ y ∧ y ≤ x ∧ 1 ≤ x := Iff.rfl
example : GlobalEquivalence transitiveSource withMargin := withMargin.equivalence

-- The second proof uses the first derived row in the current checkpoint.
reformulation chainedMargin : transitiveSource := by
  derive margin : 1 ≤ x using marginOfFeasible
  derive positive : 0 < x using (by
    intro point hp
    exact lt_of_lt_of_le zero_lt_one hp.2.2)

example (y x : ℝ) : chainedMargin.feasible (y, x) ↔
    1 ≤ y ∧ y ≤ x ∧ 1 ≤ x ∧ 0 < x := Iff.rfl
example : GlobalEquivalence transitiveSource chainedMargin := chainedMargin.equivalence

reformulation exponential : transitiveSource := by
  derive margin : 1 ≤ x using marginOfFeasible
  substitute x := Real.exp u

example (y u : ℝ) : exponential.objective (y, u) = u := rfl
example (y u : ℝ) : exponential.feasible (y, u) ↔
    1 ≤ y ∧ y ≤ Real.exp u ∧ 1 ≤ Real.exp u := Iff.rfl
example : GlobalEquivalence transitiveSource exponential := exponential.equivalence

/--
info: problem (y u : ℝ)
  maximize u
  subject to
    lower : 1 ≤ y
    ordered : y ≤ Real.exp u
    margin : 1 ≤ Real.exp u
-/
#guard_msgs in
#printp exponential

-- Explicit whole-problem coverage sees the newly appended row as well.
def exponentialCoverage :
    FeasibleSurjection withMargin (fun point : ℝ × ℝ => (point.1, Real.exp point.2)) where
  preimage point := (point.1.1, Real.log point.1.2)
  rightInverse point := by
    apply Prod.ext
    · rfl
    · exact Real.exp_log (lt_of_lt_of_le zero_lt_one point.2.2.2)

reformulation explicitlyCovered : transitiveSource := by
  derive margin : 1 ≤ x using marginOfFeasible
  substitute x := Real.exp u using exponentialCoverage

example : explicitlyCovered = exponential := rfl
example : GlobalEquivalence transitiveSource explicitlyCovered := explicitlyCovered.equivalence

def interval :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

-- Explicit True rows remain visible through later normalization, and a
-- conjunction stays a single named row rather than splitting its labels.
reformulation explicitRowsRetained : interval := by
  derive tag : True using (by intro _ _; trivial)
  derive grouped : x ≤ 1 ∧ True using (by
    intro point hp
    exact ⟨hp.2.1, True.intro⟩)
  substitute x := u

example (u : ℝ) : explicitRowsRetained.feasible u ↔
    -1 ≤ u ∧ u ≤ 1 ∧ True ∧ (u ≤ 1 ∧ True) := Iff.rfl

/--
info: problem (u : ℝ)
  minimize u
  subject to
    lower : -1 ≤ u
    upper : u ≤ 1
    tag : True
    grouped : u ≤ 1 ∧ True
-/
#guard_msgs in
#printp explicitRowsRetained

theorem absoluteBound : ∀ point, interval.feasible point → |point| ≤ 1 := by
  intro point hp
  exact abs_le.mpr hp

def quadratic := problem (x : ℝ) minimize x ^ 2

reformulation afterEpigraph : quadratic := by
  epigraph t as objective_bound
  derive relaxed_bound : x ^ 2 ≤ t + 1 using (by
    intro point hp
    change True ∧ point.1 ^ 2 ≤ point.2 at hp
    exact hp.2.trans (le_add_of_nonneg_right zero_le_one))

example (x t : ℝ) : afterEpigraph.feasible (x, t) ↔
    x ^ 2 ≤ t ∧ x ^ 2 ≤ t + 1 := Iff.rfl
example : GlobalEquivalence quadratic afterEpigraph := afterEpigraph.equivalence

reformulation afterHypograph : transitiveSource := by
  hypograph t as objective_bound
  derive margin : 1 ≤ x using (by
    intro point hp
    change (1 ≤ point.1.1 ∧ point.1.1 ≤ point.1.2) ∧
      point.2 ≤ Real.log point.1.2 at hp
    exact hp.1.1.trans hp.1.2)

example (y x t : ℝ) : afterHypograph.feasible ((y, x), t) ↔
    1 ≤ y ∧ y ≤ x ∧ t ≤ Real.log x ∧ 1 ≤ x := Iff.rfl
example : GlobalEquivalence transitiveSource afterHypograph := afterHypograph.equivalence

def middleSource :=
  problem (a x b : ℝ)
    minimize a + x + b
    subject to domain : 0 ≤ x

-- Substitution removes the transformed domain row. Derivation appends only
-- its explicitly requested row, and does not resurrect the old presentation.
reformulation afterMiddleSubstitution : middleSource := by
  substitute x := u ^ 2
  derive square_fact : 0 ≤ u ^ 2 using (by
    intro point _
    exact sq_nonneg point.1.2)

example (a u b : ℝ) : afterMiddleSubstitution.objective ((a, u), b) = a + u ^ 2 + b := rfl
example (a u b : ℝ) : afterMiddleSubstitution.feasible ((a, u), b) ↔ 0 ≤ u ^ 2 := Iff.rfl
example : GlobalEquivalence middleSource afterMiddleSubstitution :=
  afterMiddleSubstitution.equivalence

/--
info: problem (a u b : ℝ)
  minimize a + u ^ 2 + b
  subject to
    square_fact : 0 ≤ u ^ 2
-/
#guard_msgs in
#printp afterMiddleSubstitution

section
variable (t : ∀ x : ℝ, x = x) (u : ℝ)

-- Proof-only parameters and unrelated section locals do not reserve decision names.
reformulation proofOnlyParameter : free := by
  derive reflexive : x = x using (fun point _ => t point)
  epigraph t
  substitute x := u

example : GlobalEquivalence free proofOnlyParameter := proofOnlyParameter.equivalence t
example (x t : ℝ) : proofOnlyParameter.feasible (x, t) ↔ x = x ∧ x ≤ t := Iff.rfl
end

def shiftedFamily (offset : ℝ) :=
  problem (x : ℝ)
    let shifted := x + offset
    let doubled := shifted + shifted
    minimize shifted
    subject to lower : 0 ≤ shifted

theorem doubledNonnegative (offset : ℝ) :
    ∀ point, (shiftedFamily offset).feasible point → 0 ≤ (point + offset) + (point + offset) := by
  intro point hp
  exact add_nonneg hp hp

section
variable (offset : ℝ)

reformulation shiftedDerived : (shiftedFamily offset) := by
  derive doubled_nonnegative : 0 ≤ doubled using doubledNonnegative offset

example : GlobalEquivalence (shiftedFamily offset) (shiftedDerived offset) :=
  shiftedDerived.equivalence offset
example (x : ℝ) : (shiftedDerived offset).feasible x ↔
    0 ≤ x + offset ∧ 0 ≤ (x + offset) + (x + offset) := Iff.rfl

/--
info: problem (x : ℝ)
  let shifted := x + offset
  let doubled := shifted + shifted
  minimize shifted
  subject to
    lower : 0 ≤ shifted
    doubled_nonnegative : 0 ≤ doubled
-/
#guard_msgs in
#printp shiftedDerived
end

def dependentDefinitions :=
  problem (x : ℝ)
    let count := 1
    let samples : Fin count → ℝ := fun _ => x
    minimize x

reformulation afterDependentDefinitions : dependentDefinitions := by
  derive sampled : samples 0 = x using (by intro _ _; rfl)

example (x : ℝ) : afterDependentDefinitions.feasible x ↔ x = x := Iff.rfl

section
variable {α : Type*} [AddZeroClass α]

def genericSource :=
  problem (x : α)
    minimize (0 : ℝ)
    subject to reflexive : x = x

reformulation anonymousInstance : (genericSource (α := α)) := by
  derive zero_identity : x + 0 = x using (by intro point _; exact add_zero point)

example (x : α) : (anonymousInstance (α := α)).feasible x ↔
    x = x ∧ x + 0 = x := Iff.rfl
example : GlobalEquivalence (genericSource (α := α)) (anonymousInstance (α := α)) :=
  anonymousInstance.equivalence
end

namespace Hygiene

def cap (x : ℝ) : Prop := x ≤ 4

def source :=
  problem (x : ℝ)
    minimize x
    subject to upper : cap x

reformulation target : source := by
  derive copied : cap x using (by intro _ hp; exact hp)

-- Labels occupy the constraint namespace, even when the same identifier is
-- already a declaration. They do not replace or create Lean declarations.
reformulation declaredLabel : source := by
  derive cap : True using (by intro _ _; trivial)

example : cap 4 := le_rfl

macro "deriveSelf " target:ident " from " source:ident : command =>
  `(reformulation $target : $source := by
      derive macro_fact : True using (by intro _ _; trivial))

deriveSelf macroTarget from source
example : GlobalEquivalence source macroTarget := macroTarget.equivalence

end Hygiene

end
end MorewTest.Reformulation.Derive
