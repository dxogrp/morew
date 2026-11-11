/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic

/-! # User-selected constraint removal and current retained evidence -/

namespace MorewTest.Reformulation.Remove

open Morew
noncomputable section

def bounded :=
  problem (x : ℝ)
    let shifted := x + 1
    minimize shifted
    subject to
      first : 0 ≤ x
      copied : 0 ≤ x
      tag : True
      upper : shifted ≤ 4
      last : shifted ≤ 4

reformulation shortened : bounded := by
  remove at first
  remove at tag
  remove at last

example (x : ℝ) : shortened.feasible x ↔ 0 ≤ x ∧ x + 1 ≤ 4 := Iff.rfl
example (x : ℝ) : shortened.objective x = x + 1 := rfl
example : GlobalEquiv bounded shortened := shortened.equiv

/--
info: problem (x : ℝ)
  let shifted := x + 1
  minimize shifted
  subject to
    copied : 0 ≤ x
    upper : shifted ≤ 4
-/
#guard_msgs in
#printp shortened

-- Deletion releases the label, preserves untouched duplicates, and takes place
-- at the selected position rather than moving neighboring rows to the tail.
reformulation reused : bounded := by
  remove at copied
  rename first to copied
  derive first : 0 ≤ x using (by intro point hp; exact hp.1)
  remove at first
  remove at tag
  substitute x := u

example (u : ℝ) : reused.feasible u ↔ 0 ≤ u ∧ u + 1 ≤ 4 ∧ u + 1 ≤ 4 := Iff.rfl

def tautologies :=
  problem (x : ℝ)
    minimize x
    subject to
      truth : True
      equal : x = x
      ordered : x ≤ x
      reversed : x ≥ x
      exponential : 0 < Real.exp x
      square : 0 ≤ x ^ 2
      grouped : (True ∧ x = x) ∧ (x ≤ x ∧ (0 < Real.exp x ∧ 0 ≤ x ^ 2))

reformulation unconstrained : tautologies := by
  remove at truth
  remove at equal
  remove at ordered
  remove at reversed
  remove at exponential
  remove at square
  remove at grouped

example (x : ℝ) : unconstrained.feasible x ↔ True := Iff.rfl
example : GlobalEquiv tautologies unconstrained := unconstrained.equiv

/-- info: problem (x : ℝ)
  minimize x -/
#guard_msgs in
#printp unconstrained

def Nonneg (x : ℝ) := 0 ≤ x

def aliases :=
  problem (x : ℝ)
    let unchanged := x
    minimize x
    subject to
      first : Nonneg unchanged
      second : 0 ≤ x
      grouped : 0 ≤ x ∧ x ≤ 1
      copy_grouped : 0 ≤ unchanged ∧ unchanged ≤ 1
      retained : True

reformulation aliasRemoved : aliases := by
  remove at first
  remove at copy_grouped

example (x : ℝ) : aliasRemoved.feasible x ↔ 0 ≤ x ∧ (0 ≤ x ∧ x ≤ 1) ∧ True := Iff.rfl

def interval :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1
      relaxed : x ≤ 3

theorem relaxedOfInterval : ∀ x : ℝ, (-1 ≤ x ∧ x ≤ 1) → x ≤ 3 := by
  intro x hx
  exact hx.2.trans (by norm_num)

theorem relaxedOfIntervalAt (bound : ℝ) (hbound : 1 ≤ bound) :
    ∀ x : ℝ, (-1 ≤ x ∧ x ≤ 1) → x ≤ bound := by
  intro x hx
  exact hx.2.trans hbound

reformulation explicitNamed : interval := by
  remove at relaxed using relaxedOfInterval

reformulation explicitApplied : interval := by
  remove at relaxed using relaxedOfIntervalAt 3 (by norm_num)

reformulation explicitInline : interval := by
  remove at relaxed using (by intro point hp; exact hp.2.trans (by norm_num))

example : explicitApplied = explicitNamed := rfl
example : explicitInline = explicitNamed := rfl
example (x : ℝ) : explicitNamed.feasible x ↔ -1 ≤ x ∧ x ≤ 1 := Iff.rfl

-- Named conjunctions are single rows. Projection is possible with an explicit
-- proof, and does not expand the automatic duplicate policy.
reformulation explicitProjection : aliases := by
  remove at first
  remove at second using (by intro point hp; exact hp.1.1)
  remove at grouped

example (x : ℝ) : explicitProjection.feasible x ↔ (0 ≤ x ∧ x ≤ 1) ∧ True := Iff.rfl

def impossible :=
  problem (x : ℝ)
    minimize x
    subject to
      contradiction : False
      arbitrary : 0 ≤ x

reformulation infeasible : impossible := by
  remove at arbitrary using (by intro _ hp; exact hp.elim)

example (x : ℝ) : infeasible.feasible x ↔ False := Iff.rfl
example : GlobalEquiv impossible infeasible := infeasible.equiv

section Generic
variable {X V : Type*} [Preorder V] (f : X → V) (P : X → Prop)

def generic :=
  problem (point : X)
    minimize f point
    subject to
      original : P point
      repeated : P point
      reflexive : point = point

reformulation genericRemoved : (generic f P) := by
  remove at original
  remove at reflexive

example (x : X) : (genericRemoved f P).feasible x ↔ P x := Iff.rfl
example (x : X) : (genericRemoved f P).objective x = f x := rfl
example : GlobalEquiv (generic f P) (genericRemoved f P) :=
  genericRemoved.equiv f P
end Generic

section GenericOrder
variable {X : Type*} [Preorder X]

def orderedGeneric :=
  problem (point : X)
    minimize (0 : Nat)
    subject to
      reflexive : point ≤ point
      reversed : point ≥ point

reformulation orderedGenericRemoved : (orderedGeneric (X := X)) := by
  remove at reflexive
  remove at reversed

example (x : X) : (orderedGenericRemoved (X := X)).feasible x ↔ True := Iff.rfl
end GenericOrder

def maximum :=
  problem (x : ℝ)
    maximize x
    subject to
      cap : x ≤ 1
      copied : x ≤ 1
      tag : True

reformulation maximumBound : maximum := by
  remove at copied
  hypograph t as bound
  remove at tag
  derive redundant : t ≤ x using (by intro point hp; exact hp.2)
  remove at redundant

example (x t : ℝ) : maximumBound.feasible (x, t) ↔ x ≤ 1 ∧ t ≤ x := Iff.rfl
example (x t : ℝ) : maximumBound.objective (x, t) = t := rfl
example : GlobalEquiv maximum maximumBound := maximumBound.equiv

def positive :=
  problem (x y : ℝ)
    minimize Real.log x + Real.log y
    subject to
      domain_x : 0 < x
      first : x ≤ 3
      duplicate : x ≤ 3
      domain_y : 0 < y
      tag : True
      grouped : y ≤ 4 ∧ True

-- The checkpoint inventory is already sparse before explicit removal. New
-- checkpoints must not resurrect removed domains, even after their labels are reused.
reformulation checkpointChain : positive := by
  substitute x := Real.exp u
  remove at duplicate
  rename first to domain_x
  substitute y := Real.exp v
  remove at tag
  derive domain_y : True using (by intro _ _; trivial)
  remove at domain_y
  epigraph t as objective_bound
  substitute u := w

example (w v t : ℝ) : checkpointChain.feasible ((w, v), t) ↔
    Real.exp w ≤ 3 ∧ (Real.exp v ≤ 4 ∧ True) ∧ w + v ≤ t := Iff.rfl

def zero := problem (_x : ℝ) minimize (0 : ℝ) subject to tag : True

reformulation zeroChain : zero := by
  epigraph t as bound
  substitute t := u ^ 2
  remove at tag
  derive bound : 0 ≤ u ^ 2 using (by intro point _; exact sq_nonneg point.2)
  remove at bound
  epigraph s as bound

example (x u s : ℝ) : zeroChain.feasible ((x, u), s) ↔ u ^ 2 ≤ s := Iff.rfl

reformulation zeroEpiWithoutTag : zero := by
  epigraph t as bound
  remove at tag

def zeroEpiCoverage : FeasibleSurjection zeroEpiWithoutTag
    (fun point : ℝ × ℝ => (point.1, point.2 ^ 2)) where
  preimage point := (point.1.1, Real.sqrt point.1.2)
  rightInverse point := Prod.ext rfl (Real.sq_sqrt point.2)

def zeroEpiRepair := zeroEpiCoverage.restrictionImprovement
  (fun point => 0 ≤ point.2) (fun point => Real.sqrt_nonneg point.1.2)

-- Removing a row establishes a canonical source. Later explicit coverage sees
-- that source; the subsequent restriction still sees the substitution's raw pullback.
reformulation zeroExplicit : zero := by
  epigraph t as bound
  remove at tag
  substitute t := u ^ 2 using zeroEpiCoverage
  restrict branch : 0 ≤ u using zeroEpiRepair

example (x u : ℝ) : zeroExplicit.feasible (x, u) ↔ 0 ≤ u := Iff.rfl
example : GlobalEquiv zero zeroExplicit := zeroExplicit.equiv

def trueRepair {X V : Type*} [Preorder V] (p : Problem X V) :
    GlobalImprovement p (p.addConstraint (fun _ => True)) where
  map point := ⟨point.1, point.2, True.intro⟩
  objective_le _ := le_rfl

reformulation afterRestriction : explicitNamed := by
  restrict temporary : True using trueRepair explicitNamed
  remove at temporary
  substitute x := u

example : afterRestriction = explicitNamed := rfl

def positiveWithTag :=
  problem (x : ℝ)
    minimize Real.log x
    subject to
      positive : 0 < x
      tag : True

reformulation retainedPositive : positiveWithTag := by
  remove at tag

def retainedCoverage : FeasibleSurjection retainedPositive (fun u : ℝ => Real.exp u) where
  preimage point := Real.log point.1
  rightInverse point := Real.exp_log point.2

reformulation explicitAfterRemoval : positiveWithTag := by
  remove at tag
  substitute x := Real.exp u using retainedCoverage

example (u : ℝ) : explicitAfterRemoval.feasible u ↔ True := Iff.rfl
example (u : ℝ) : explicitAfterRemoval.objective u = u := rfl

reformulation repairAfterRemoval : positiveWithTag := by
  remove at tag
  restrict tag : True using trueRepair retainedPositive
  remove at tag

example : repairAfterRemoval = retainedPositive := rfl

def labels :=
  problem (x : ℝ)
    minimize x
    subject to
      cap : x ≤ 3
      labels.cap : x ≤ 3
      «cap.with.dot» : x ≤ 3
      «remove» : True

reformulation labelRemoval : labels := by
  remove at labels.cap
  remove at «cap.with.dot»
  remove at «remove»
  rename cap to labels.cap

example (x : ℝ) : labelRemoval.feasible x ↔ x ≤ 3 := Iff.rfl

section
variable (offset : ℝ)

def family :=
  problem (x : ℝ)
    let shifted := x + offset
    let family : Fin 2 → ℝ := fun _ => shifted
    minimize shifted
    subject to
      bound : 0 ≤ family 0
      duplicate : 0 ≤ shifted
      tag : True

reformulation familyRemoved : (family offset) := by
  remove at duplicate
  remove at tag

example (x : ℝ) : (familyRemoved offset).feasible x ↔ 0 ≤ x + offset := Iff.rfl
end

namespace Hygiene
def cap (x : ℝ) : Prop := x ≤ 3
def source :=
  problem (x : ℝ)
    minimize x
    subject to
      cap : cap x
      copied : cap x

reformulation target : source := by
  remove at copied
end Hygiene

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
    subject to
      original : right ≤ x
      copy : right ≤ x
      upper : x ≤ left

reformulation target : (@source first second) := by
  remove at original

example (x : ℝ) : (@target first second).objective x = @Parameter.value first + x := rfl
example (x : ℝ) : (@target first second).feasible x ↔
    @Parameter.value second ≤ x ∧ x ≤ @Parameter.value first := Iff.rfl
end Instances

run_cmd do
  for (name, expected) in #[
      (``shortened, #[`copied, `upper]),
      (``reused, #[`copied, `upper, `last]),
      (``unconstrained, #[]),
      (``aliasRemoved, #[`second, `grouped, `retained]),
      (``explicitNamed, #[`lower, `upper]),
      (``explicitProjection, #[`copy_grouped, `retained]),
      (``infeasible, #[`contradiction]),
      (``maximumBound, #[`cap, `bound]),
      (``checkpointChain, #[`domain_x, `grouped, `objective_bound]),
      (``zeroChain, #[`bound]),
      (``afterRestriction, #[`lower, `upper]),
      (``labelRemoval, #[`labels.cap]),
      (``familyRemoved, #[`bound])] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing removal presentation for {name}"
    let actual := view.constraints.map (·.name.eraseMacroScopes)
    unless actual == expected do
      Lean.throwError "unexpected labels after removal for {name}: {actual}; expected {expected}"

end
end MorewTest.Reformulation.Remove
