/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Affine.HelperFixtures
import MorewTest.Affine.Support
import MorewTest.Reformulation.AffineHelperSource

/-!
# Affine helper certification in conic reformulations

Helper expansion supplies affine certificates without changing model-local
definitions, printed expressions, or the native heads accepted by conic rules.
Finite evidence inside imported helpers remains available across the model.
-/

namespace MorewTest.Reformulation.AffineHelpers

open Morew Morew.Conic MorewTest.Affine.HelperFixtures

noncomputable section

def minimum :=
  problem (x : ℝ)
    let loss := cost 2 1 x
    let penalty := residual 3 2 x
    minimize loss + penalty
    subject to
      cap : loss ≤ 10
      lower : -5 ≤ penalty

reformulation minimumTarget : minimum := by
  conic

example : GlobalEquivalence minimum minimumTarget := minimumTarget.equivalence
example : IsConic minimumTarget := minimumTarget.isConic
example : minimumTarget.conicForm.data.sense = .minimize := rfl
example : minimumTarget.conicForm.data.rowCount = 2 := rfl
example (x : ℝ) : minimumTarget.objective x = cost 2 1 x + residual 3 2 x := rfl
example (x : ℝ) : minimumTarget.feasible x ↔
    cost 2 1 x ≤ 10 ∧ -5 ≤ residual 3 2 x := Iff.rfl

/--
info: problem (x : ℝ)
  let loss := cost 2 1 x
  let penalty := Affine.HelperFixtures.residual 3 2 x
  minimize loss + penalty
  subject to
    cap : loss ≤ 10
    lower : -5 ≤ penalty
-/
#guard_msgs in
#printp minimumTarget

section

variable (offset : ℝ)

def maximum :=
  problem (x : ℝ)
    maximize cost 2 offset x
    subject to
      cap : residual 3 offset x ≤ 10

reformulation maximumTarget : (maximum offset) := by
  conic

example : GlobalEquivalence (maximum offset) (maximumTarget offset) :=
  maximumTarget.equivalence offset
example : IsConic (maximumTarget offset) := maximumTarget.isConic offset
example : (maximumTarget.conicForm offset).data.sense = .maximize := rfl

end

reformulation concreteMaximum : (maximum 4) := by
  conic

/--
info: problem (x : ℝ)
  maximize cost 2 4 x
  subject to
    cap : Affine.HelperFixtures.residual 3 4 x ≤ 10
-/
#guard_msgs in
#printp concreteMaximum

reformulation importedTarget : (AffineHelperSource.source 2 3) := by
  conic

example : GlobalEquivalence (AffineHelperSource.source 2 3) importedTarget :=
  importedTarget.equivalence
example : IsConic importedTarget := importedTarget.isConic
example (x : ℝ) : importedTarget.objective x = cost 2 3 x := rfl
example (x : ℝ) : importedTarget.feasible x ↔ cost 2 3 x ≤ 10 ∧ 0 ≤ cost 1 0 x := Iff.rfl

/--
info: problem (x : ℝ)
  let loss := cost 2 3 x
  minimize loss
  subject to
    cap : loss ≤ 10
    lower : 0 ≤ cost 1 0 x
-/
#guard_msgs in
#printp importedTarget

-- Expanding a helper in the first operand must not hide the existing structural
-- reduction of a later problem projection. Both operand orders certify.
run_cmd Lean.Elab.Command.liftTermElabM do
  MorewTest.Affine.assertAffine (← `(fun x : ℝ =>
    (AffineHelperSource.source 2 3).objective x + cost 2 1 x))
  MorewTest.Affine.assertAffine (← `(fun x : ℝ =>
    cost 2 1 x + (AffineHelperSource.source 2 3).objective x))

def nativeAtoms :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to
      absolute : |residual 2 1 x| ≤ cost 1 0 t
      square : cost 2 1 x ^ 2 ≤ cost 1 0 t
      exponential : Real.exp (residual 2 1 x) ≤ cost 1 0 t

reformulation nativeAtomsTarget : nativeAtoms := by
  conic at absolute
  conic at square
  conic at exponential
  conic

example : GlobalEquivalence nativeAtoms nativeAtomsTarget := nativeAtomsTarget.equivalence
example : IsConic nativeAtomsTarget := nativeAtomsTarget.isConic
example : nativeAtomsTarget.conicForm.data.rowCount = 4 := rfl
example (x t : ℝ) : nativeAtomsTarget.feasible (x, t) ↔
    residual 2 1 x ≤ cost 1 0 t ∧ -(residual 2 1 x) ≤ cost 1 0 t ∧
      (cost 1 0 t, 1 / 2, ![cost 2 1 x]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      (residual 2 1 x, 1, cost 1 0 t) ∈ EXP := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize cost 2 1 x
  subject to
    absolute_conic_1 : Affine.HelperFixtures.residual 2 1 x ≤ cost 1 0 t
    absolute_conic_2 : -Affine.HelperFixtures.residual 2 1 x ≤ cost 1 0 t
    square_conic_1 : (cost 1 0 t, 1 / 2, ![cost 2 1 x]) ∈ RSOC 1
    exponential_conic_1 : (Affine.HelperFixtures.residual 2 1 x, 1, cost 1 0 t) ∈ EXP
-/
#guard_msgs in
#printp nativeAtomsTarget

namespace Boundaries

def wrappedAbs (x : ℝ) := |x|
def wrappedSquare (x : ℝ) := x ^ 2
def wrappedExp (x : ℝ) := Real.exp x
def wrappedPredicate (x t : ℝ) : Prop := cost 2 1 x ≤ t

elab "assert_helper_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let `(command| reformulation $target:ident : $_source:ident
      $[certificate $_alias:ident]? := by $_steps:reformulationStep*) := nested
    | Lean.throwError "expected a reformulation command"
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  for (name, _) in after.constants.toList do
    unless before.contains name do
      Lean.throwError m!"failed helper certification leaked declaration {name}"
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed helper certification leaked presentation metadata"

def absoluteSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to bound : wrappedAbs x ≤ t

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
assert_helper_atomic%
reformulation noWrappedAbsolute : absoluteSource := by
  conic at bound

def squareSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to bound : wrappedSquare x ≤ t

/-- error: terminal conic validation is uncertified: constraint `bound`: -/
#guard_msgs (substring := true) in
assert_helper_atomic%
reformulation noWrappedSquare : squareSource := by
  conic

def exponentialSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to
      first : |cost 2 1 x| ≤ t
      bound : wrappedExp x ≤ t

/-- error: constraint `bound`: -/
#guard_msgs (substring := true) in
assert_helper_atomic%
reformulation noWrappedExponential : exponentialSource certificate noWrappedAlias := by
  conic at first
  conic at bound

def predicateSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to bound : wrappedPredicate x t

/-- error: terminal conic validation is uncertified: constraint `bound`: -/
#guard_msgs (substring := true) in
assert_helper_atomic%
reformulation noWrappedPredicate : predicateSource := by
  conic

-- Option changes take effect at the model command and do not escape its scope.
set_option morew.affine.maxExpansionSteps 0 in
/-- error: terminal conic validation is uncertified: objective: -/
#guard_msgs (substring := true) in
assert_helper_atomic%
reformulation helpersDisabled : minimum := by
  conic

reformulation helpersReenabled : minimum := by
  conic

example : IsConic helpersReenabled := helpersReenabled.isConic

end Boundaries

end
end MorewTest.Reformulation.AffineHelpers
