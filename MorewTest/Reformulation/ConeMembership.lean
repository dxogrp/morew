/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import MorewTest.Reformulation.ConeMembership.Defined

/-!
# Membership targets from final conic conversion

Check the actual feasibility predicates as well as their presentations. Named
groups, helper references, and distinct local aliases survive final conversion
and continuation from an imported, applied target.
-/

namespace MorewTest.Reformulation.ConeMembership

open Morew Morew.Conic
noncomputable section

def scalars :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      bounds : (0 ≤ x ∧ True) ∧ (x ≤ 0 ∧ y ≥ x)
      equality : x = y
      rightZero : x = 0
      leftZero : 0 = y
      retainedOperands : x + 0 ≤ y - 0
      budget : 2 * x + 1 ≤ 3 * y + 4
      empty : True ∧ True

reformulation scalarTarget : scalars := by
  conic

example : GlobalEquivalence scalars scalarTarget := scalarTarget.equivalence
example : scalarTarget.conicForm.data.toProblem = scalarTarget :=
  scalarTarget.conicForm.represents
example : scalarTarget.conicForm.data.rowCount = 8 := rfl
example (x y : ℝ) : scalarTarget.feasible (x, y) ↔
    ((x ∈ ℝ₊ ∧ True) ∧ (-x ∈ ℝ₊ ∧ y - x ∈ ℝ₊)) ∧
      x - y ∈ ({0} : Set ℝ) ∧ x ∈ ({0} : Set ℝ) ∧ -y ∈ ({0} : Set ℝ) ∧
        (y - 0) - (x + 0) ∈ ℝ₊ ∧ (3 * y + 4) - (2 * x + 1) ∈ ℝ₊ ∧
          (True ∧ True) := Iff.rfl

/--
info: problem (x y : ℝ)
  minimize x + y
  subject to
    bounds : (x ∈ ℝ₊ ∧ True) ∧ -x ∈ ℝ₊ ∧ y - x ∈ ℝ₊
    equality : x - y ∈ ({0} : Set ℝ)
    rightZero : x ∈ ({0} : Set ℝ)
    leftZero : -y ∈ ({0} : Set ℝ)
    retainedOperands : y - 0 - (x + 0) ∈ ℝ₊
    budget : 3 * y + 4 - (2 * x + 1) ∈ ℝ₊
    empty : True ∧ True
-/
#guard_msgs in
#printp scalarTarget

def zeroAlias :=
  problem (x : ℝ)
    let z := (0 : ℝ)
    minimize x
    subject to
      upper : x ≤ z
      lower : z ≤ x

reformulation zeroAliasTarget : zeroAlias := by
  conic

example : zeroAliasTarget.conicForm.data.toProblem = zeroAliasTarget :=
  zeroAliasTarget.conicForm.represents

/--
info: problem (x : ℝ)
  let z := 0
  minimize x
  subject to
    upper : z - x ∈ ℝ₊
    lower : x - z ∈ ℝ₊
-/
#guard_msgs in
#printp zeroAliasTarget

def numeric :=
  problem (x : ℝ)
    minimize x
    subject to
      comparisons : (2 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ 2
      equalities : (2 : ℝ) = 2 ∧ (2 : ℝ) = 3

reformulation numericTarget : numeric := by
  conic

example : GlobalEquivalence numeric numericTarget := numericTarget.equivalence
example : numericTarget.conicForm.data.rowCount = 4 := rfl
example : numericTarget.conicForm.data.toProblem = numericTarget := numericTarget.conicForm.represents
example (x : ℝ) : numericTarget.feasible x ↔
    (3 - 2 ∈ ℝ₊ ∧ 2 - 3 ∈ ℝ₊) ∧
      (2 - 2 ∈ ({0} : Set ℝ) ∧ 2 - 3 ∈ ({0} : Set ℝ)) := Iff.rfl

/--
info: problem (x : ℝ)
  minimize x
  subject to
    comparisons : 3 - 2 ∈ ℝ₊ ∧ 2 - 3 ∈ ℝ₊
    equalities : 2 - 2 ∈ ({0} : Set ℝ) ∧ 2 - 3 ∈ ({0} : Set ℝ)
-/
#guard_msgs in
#printp numericTarget

-- Check expression heads without unfolding membership or the cone carrier;
-- semantic equivalence alone would also accept an unchanged comparison.
run_cmd Lean.Elab.Command.liftTermElabM do
  let declaration ← Lean.getConstInfo ``scalarTarget
  let some value := declaration.value? | throwError "missing membership target"
  unless (value.find? (·.isConstOf ``Membership.mem)).isSome do
    throwError "final target has no membership predicates"
  for head in #[``LE.le, ``LT.lt] do
    if (value.find? (·.isConstOf head)).isSome then
      throwError "final target still contains an affine comparison"

section
variable (n : Nat)

def vectors :=
  problem (v w : Fin n → ℝ)
    minimize (0 : ℝ)
    subject to
      grouped : 0 ≤ v ∧ v ≤ w
      equal : v = w
      rightZero : w = 0
      leftZero : 0 = v

reformulation vectorTarget : (vectors n) := by
  conic

example : GlobalEquivalence (vectors n) (vectorTarget n) := vectorTarget.equivalence n
example : (vectorTarget.conicForm n).data.rowCount = 5 := rfl
example : (vectorTarget.conicForm n).data.toProblem = vectorTarget n :=
  (vectorTarget.conicForm n).represents
example (v w : Fin n → ℝ) : (vectorTarget n).feasible (v, w) ↔
    (v ∈ ℝ₊^n ∧ w - v ∈ ℝ₊^n) ∧
      v - w ∈ ({0} : Set (Fin n → ℝ)) ∧ w ∈ ({0} : Set (Fin n → ℝ)) ∧
        -v ∈ ({0} : Set (Fin n → ℝ)) := Iff.rfl

end

-- Zero-dimensional comparisons still contribute structural cone rows.
example : (vectorTarget.conicForm 0).data.rowCount = 5 := rfl
example : (vectorTarget.conicForm 0).data.toProblem = vectorTarget 0 :=
  (vectorTarget.conicForm 0).represents

reformulation emptyVectorAgain : (vectorTarget 0) := by
  conic

example : emptyVectorAgain.conicForm.data.rowCount = 5 := rfl
example : GlobalEquivalence (vectorTarget 0) emptyVectorAgain := emptyVectorAgain.equivalence

def native :=
  problem (x t : ℝ) (v : Fin 0 → ℝ)
    minimize t
    subject to
      secondOrder : (t, v) ∈ SOC 0
      rotated : (t, 1, v) ∈ RSOC 0
      exponential : (x, 1, t) ∈ EXP
      family : ∀ i : Fin 0, (v i, 1, t) ∈ EXP
      affine : x ≤ t

reformulation nativeTarget : native := by
  conic

example : GlobalEquivalence native nativeTarget := nativeTarget.equivalence
example : nativeTarget.conicForm.data.rowCount = 5 := rfl
example : nativeTarget.conicForm.data.toProblem = nativeTarget := nativeTarget.conicForm.represents
example (x t : ℝ) (v : Fin 0 → ℝ) : nativeTarget.feasible ((x, t), v) ↔
    (t, v) ∈ SOC 0 ∧ (t, 1, v) ∈ RSOC 0 ∧ (x, 1, t) ∈ EXP ∧
      (∀ i : Fin 0, (v i, 1, t) ∈ EXP) ∧ t - x ∈ ℝ₊ := Iff.rfl

-- This name must not capture imported helper references during replay.
def shifted (_offset x : ℝ) : ℝ := x - 100

reformulation applied : (Defined.source 2) := by
  conic

reformulation continued : (Defined.target 3) := by
  epigraph t as objectiveBound
  conic

example : GlobalEquivalence (Defined.source 2) applied := applied.equivalence
example : GlobalEquivalence (Defined.source 3) continued :=
  (Defined.target.equivalence 3).trans continued.equivalence
example : continued.conicForm.data.toProblem = continued := continued.conicForm.represents
example (x t : ℝ) : continued.feasible (x, t) ↔
    ((Defined.shifted 3 x ∈ ℝ₊ ∧ True) ∧ 4 - Defined.shifted 3 x ∈ ℝ₊) ∧
      Defined.shifted 3 x - Defined.shifted 3 x ∈ ({0} : Set ℝ) ∧
        t - Defined.shifted 3 x ∈ ℝ₊ := Iff.rfl

/--
info: problem (x t : ℝ)
  let first := Defined.shifted 3 x
  let second := Defined.shifted 3 x
  let unused := x - 3
  minimize t
  subject to
    grouped : (first ∈ ℝ₊ ∧ True) ∧ 4 - second ∈ ℝ₊
    same : first - second ∈ ({0} : Set ℝ)
    objectiveBound : t - first ∈ ℝ₊
-/
#guard_msgs in
#printp continued

run_cmd do
  for name in #[``applied, ``continued] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing imported membership presentation"
    unless view.definitions.map (·.name.eraseMacroScopes) == #[`first, `second, `unused] do
      Lean.throwError "final conversion changed local binding identity or order"
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``continued
    | Lean.throwError "missing continued membership presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) == #[`grouped, `same, `objectiveBound] do
    Lean.throwError "final conversion split or renamed an affine group"
  for (source, copied) in #[(``continued, `replayed),
      (``numericTarget, `replayedNumeric), (``emptyVectorAgain, `replayedEmptyVector)] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) source
      | Lean.throwError "missing membership presentation for replay"
    let term ← Lean.Elab.liftMacroM view.toTermSyntax
    let name := Lean.mkIdent copied
    Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x t : ℝ) : replayed.feasible (x, t) ↔ continued.feasible (x, t) := Iff.rfl
example (x : ℝ) : replayedNumeric.feasible x ↔ numericTarget.feasible x := Iff.rfl
example (v w : Fin 0 → ℝ) :
    replayedEmptyVector.feasible (v, w) ↔ emptyVectorAgain.feasible (v, w) := Iff.rfl

-- Generated zero and subtraction use canonical instances even if an unrelated
-- local definition retains a custom instance parameter. Stored presentation
-- replay must keep those exact instances as well as the readable binding names.
namespace AmbientZero
section
variable [customZero : Zero ℝ]

def source :=
  problem (x y : ℝ)
    let unused : ℝ := 0
    minimize x
    subject to
      equal : x = y

reformulation target : source := by
  conic

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing membership presentation under a custom zero instance"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x y : ℝ) : replayed.feasible (x, y) ↔ target.feasible (x, y) := Iff.rfl
example : target.conicForm.data.toProblem = target := target.conicForm.represents

reformulation continued : target := by
  conic

example : GlobalEquivalence target continued := continued.equivalence

end
end AmbientZero

namespace AmbientSubtraction
section
variable [customSub : HSub ℝ ℝ ℝ]

def source :=
  problem (x y : ℝ)
    let unused : ℝ := x - y
    minimize x
    subject to
      equal : x = y

reformulation target : source := by
  conic

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing membership presentation under a custom subtraction instance"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x y : ℝ) : replayed.feasible (x, y) ↔ target.feasible (x, y) := Iff.rfl
example : target.conicForm.data.toProblem = target := target.conicForm.represents

reformulation continued : target := by
  conic

example : GlobalEquivalence target continued := continued.equivalence

end
end AmbientSubtraction

end
end MorewTest.Reformulation.ConeMembership
