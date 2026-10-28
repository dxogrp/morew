/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics
import Morew.Elab.Conic.Rewrite
import MorewTest.Affine.HelperFixtures
import MorewTest.Affine.Support
import MorewTest.Reformulation.AffineHelperSource
import MorewTest.Environment
import Morew.Elab.Expr

/-!
# Affine helper certification in conic reformulations

Helper expansion supplies affine certificates while preserving model-local
definitions, helper references, and the native heads accepted by conic rules.
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
    10 - cost 2 1 x ∈ ℝ₊ ∧ residual 3 2 x + 5 ∈ ℝ₊ := Iff.rfl

/--
info: problem (x : ℝ)
  let loss := cost 2 1 x
  let penalty := Affine.HelperFixtures.residual 3 2 x
  minimize loss + penalty
  subject to
    cap : 10 - loss ∈ ℝ₊
    lower : penalty + 5 ∈ ℝ₊
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
    cap : 10 - Affine.HelperFixtures.residual 3 4 x ∈ ℝ₊
-/
#guard_msgs in
#printp concreteMaximum

reformulation importedTarget : (AffineHelperSource.source 2 3) := by
  conic

example : GlobalEquivalence (AffineHelperSource.source 2 3) importedTarget :=
  importedTarget.equivalence
example : IsConic importedTarget := importedTarget.isConic
example (x : ℝ) : importedTarget.objective x = cost 2 3 x := rfl
example (x : ℝ) : importedTarget.feasible x ↔
    10 - cost 2 3 x ∈ ℝ₊ ∧ cost 1 0 x ∈ ℝ₊ := Iff.rfl

/--
info: problem (x : ℝ)
  let loss := cost 2 3 x
  minimize loss
  subject to
    cap : 10 - loss ∈ ℝ₊
    lower : cost 1 0 x ∈ ℝ₊
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
    cost 1 0 t - residual 2 1 x ∈ ℝ₊ ∧ cost 1 0 t + residual 2 1 x ∈ ℝ₊ ∧
      (cost 1 0 t, 1 / 2, ![cost 2 1 x]) ∈ (Cone.rotatedSecondOrder 1).carrier ∧
      (residual 2 1 x, 1, cost 1 0 t) ∈ EXP := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize cost 2 1 x
  subject to
    absolute_conic_1 : cost 1 0 t - Affine.HelperFixtures.residual 2 1 x ∈ ℝ₊
    absolute_conic_2 : cost 1 0 t + Affine.HelperFixtures.residual 2 1 x ∈ ℝ₊
    square_conic_1 : (cost 1 0 t, 1 / 2, ![cost 2 1 x]) ∈ RSOC 1
    exponential_conic_1 : (Affine.HelperFixtures.residual 2 1 x, 1, cost 1 0 t) ∈ EXP
-/
#guard_msgs in
#printp nativeAtomsTarget

namespace TypedPlans

open Lean Lean.Meta

private def checkExact (source : Expr) (result : Morew.Elab.Conic.Plan.Result) : MetaM Unit := do
  discard <| Morew.Elab.Rewrite.Plan.checkLift source result.lift
  for proof in #[result.lift, result.targetIff] do
    if proof.hasMVar || proof.hasSorry then throwError "incomplete helper plan"
  checkWithKernel result.targetIff
  for row in result.certifiedRows do
    checkWithKernel row.constraint
    checkWithKernel row.pointwiseIff

-- These APIs receive no presentation state. They must discover hidden evidence
-- themselves, including evidence present only in an untouched retained row.
run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a : ι → ℝ) => fun x : ι → ℝ => |finiteDot e a x| ≤ 1))
  lambdaBoundedTelescope expression 3 fun _ source => do
    match ← Morew.Elab.Conic.Rewrite.planUnique source with
    | .ok (.inl result) => checkExact source result
    | .ok (.inr _) => throwError "finite evidence changed an unconditional lift into a contextual lift"
    | .error error => throwError "hidden finite polyhedral plan failed: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a : ι → ℝ) => fun x : ι → ℝ => ‖(![finiteDot e a x] : Fin 1 → ℝ)‖ ≤ 10))
  lambdaBoundedTelescope expression 3 fun _ source => do
    match ← Morew.Elab.Conic.Rewrite.planUnique source with
    | .ok (.inl result) => checkExact source result
    | .ok (.inr _) => throwError "finite evidence changed an unconditional lift into a contextual lift"
    | .error error => throwError "hidden finite norm-coordinate plan failed: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a : ι → ℝ) => fun x : ι → ℝ => ({1, 3} : Finset ℕ).sup' (by decide)
      (fun i => (i : ℝ) * finiteDot e a x) ≤ 10))
  lambdaBoundedTelescope expression 3 fun _ source => do
    match ← Morew.Elab.Conic.Rewrite.planUnique source with
    | .ok (.inl result) => checkExact source result
    | .ok (.inr _) => throwError "finite evidence changed an unconditional lift into a contextual lift"
    | .error error => throwError "hidden finite supremum-coordinate plan failed: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a : ι → ℝ) => fun x : ι → ℝ => -10 ≤ ({1, 3} : Finset ℕ).inf' (by decide)
      (fun i => (i : ℝ) * finiteDot e a x)))
  lambdaBoundedTelescope expression 3 fun _ source => do
    match ← Morew.Elab.Conic.Rewrite.planUnique source with
    | .ok (.inl result) => checkExact source result
    | .ok (.inr _) => throwError "finite evidence changed an unconditional lift into a contextual lift"
    | .error error => throwError "hidden finite infimum-coordinate plan failed: {error.reason}"

def helperTargetLift {ι : Type} (e : Fin 2 ≃ ι) (a : ι → ℝ) :
    ExactConstraintLift (fun (_x : ι → ℝ) => True) :=
  ExactConstraintLift.ofIff
    (fun x => finiteDot e a x = finiteDot e a x)
    (fun _ => ⟨fun _ => rfl, fun _ => True.intro⟩)

-- The selected predicate supplies no finite evidence at all. Only the custom
-- representation's target contains a helper carrying the needed enumeration.
run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a : ι → ℝ) => ((fun (_x : ι → ℝ) => True), helperTargetLift e a)))
  lambdaBoundedTelescope expression 3 fun _ pair => do
    let pair ← Morew.Elab.Expr.reduceStructure pair
    let source := pair.getAppArgs[2]!
    let rule := pair.getAppArgs[3]!
    match ← Morew.Elab.Conic.Rewrite.planExplicit source rule with
    | .ok (.inl result) => checkExact source result
    | .ok (.inr _) => throwError "finite evidence changed an unconditional lift into a contextual lift"
    | .error error => throwError "hidden finite explicit-target plan failed: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a : ι → ℝ) =>
      ((fun x : ι → ℝ => x (e 0) ^ 2 ≤ 1),
       (fun x : ι → ℝ => finiteDot e a x ≤ 10))))
  lambdaBoundedTelescope expression 3 fun _ pair => do
    let pair ← Morew.Elab.Expr.reduceStructure pair
    let source := pair.getAppArgs[2]!
    let retained := #[pair.getAppArgs[3]!]
    match ← Morew.Elab.Conic.Rewrite.planUnique source retained with
    | .ok (.inl result) => checkExact source result
    | .ok (.inr _) => throwError "finite evidence changed an unconditional square into a contextual lift"
    | .error error => throwError "hidden finite second-order plan failed: {error.reason}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let expression ← MorewTest.Affine.elaborate (← `(fun (ι : Type) (e : Fin 2 ≃ ι)
    (a : ι → ℝ) =>
      ((fun x : ι → ℝ => Real.exp (x (e 0)) ≤ 1),
       (fun x : ι → ℝ => finiteDot e a x ≤ 10))))
  lambdaBoundedTelescope expression 3 fun _ pair => do
    let pair ← Morew.Elab.Expr.reduceStructure pair
    let source := pair.getAppArgs[2]!
    let retained := #[pair.getAppArgs[3]!]
    match ← Morew.Elab.Conic.Rewrite.planUnique source retained with
    | .ok (.inl result) => checkExact source result
    | .ok (.inr _) => throwError "finite evidence changed an unconditional exponential into a contextual lift"
    | .error error => throwError "hidden finite exponential plan failed: {error.reason}"

end TypedPlans

namespace HiddenFinite

class Parameter where
  Index : Type
  equivalence : Fin 2 ≃ Index
  coefficients : Index → ℝ

variable [Parameter]

-- No ambient Finite or Fintype instance is installed. The only evidence lies
-- inside the imported helper in a different row from the objective and abs.
def anotherRow :=
  problem (x : Parameter.Index → ℝ) (t : ℝ)
    minimize x (Parameter.equivalence 0)
    subject to
      absolute : |x (Parameter.equivalence 0)| ≤ t
      witness : finiteDot Parameter.equivalence Parameter.coefficients x ≤ 10

reformulation anotherRowTarget : anotherRow := by
  conic

reformulation selectedRowTarget : anotherRow := by
  conic at absolute
  conic

example : GlobalEquivalence anotherRow anotherRowTarget := anotherRowTarget.equivalence
example : GlobalEquivalence anotherRow selectedRowTarget := selectedRowTarget.equivalence

-- The left operand also needs finiteness before the helper on the right is
-- independently certified; discovery must inspect the complete source row.
def oppositeOperand :=
  problem (x : Parameter.Index → ℝ)
    minimize (0 : ℝ)
    subject to
      absolute : |x (Parameter.equivalence 0)| ≤
        finiteDot Parameter.equivalence Parameter.coefficients x

reformulation oppositeOperandTarget : oppositeOperand := by
  conic at absolute
  conic

example : GlobalEquivalence oppositeOperand oppositeOperandTarget :=
  oppositeOperandTarget.equivalence

-- Native nonlinear heads remain recognition boundaries, but evidence discovery
-- must still reach the affine coordinate stored underneath the absolute value.
def nativeCoordinate :=
  problem (x : Parameter.Index → ℝ)
    minimize (0 : ℝ)
    subject to
      absolute : |finiteDot Parameter.equivalence Parameter.coefficients x| ≤ 1

reformulation nativeCoordinateTarget : nativeCoordinate := by
  conic

example : GlobalEquivalence nativeCoordinate nativeCoordinateTarget :=
  nativeCoordinateTarget.equivalence

-- Form notation needs an ambient canonical enumeration after the commands
-- have demonstrated that they recover the helper's evidence themselves.
local instance : Finite Parameter.Index := by
  let := Fintype.ofEquiv (Fin 2) Parameter.equivalence
  infer_instance
local instance : Fintype Parameter.Index := Fintype.ofFinite Parameter.Index

example : IsConic anotherRowTarget := anotherRowTarget.isConic
example : IsConic selectedRowTarget := selectedRowTarget.isConic
example : IsConic oppositeOperandTarget := oppositeOperandTarget.isConic
example : IsConic nativeCoordinateTarget := nativeCoordinateTarget.isConic
example : anotherRowTarget.conicForm.data.rowCount = 3 := rfl
example : oppositeOperandTarget.conicForm.data.rowCount = 2 := rfl
example : nativeCoordinateTarget.conicForm.data.rowCount = 2 := rfl
example : anotherRowTarget.conicForm.data.toProblem = anotherRowTarget :=
  anotherRowTarget.conicForm.represents

example (x : Parameter.Index → ℝ) (t : ℝ) : anotherRowTarget.feasible (x, t) ↔
    t - x (Parameter.equivalence 0) ∈ ℝ₊ ∧ t + x (Parameter.equivalence 0) ∈ ℝ₊ ∧
      10 - finiteDot Parameter.equivalence Parameter.coefficients x ∈ ℝ₊ := Iff.rfl

end HiddenFinite

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
  if let some name := MorewTest.newLocalDeclaration? before after then
    Lean.throwError m!"failed helper certification leaked declaration {name}"
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed helper certification leaked presentation metadata"

def absoluteSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to bound : wrappedAbs x ≤ t

#guard_error_fragments ["constraint `bound`:"] in
assert_helper_atomic%
reformulation noWrappedAbsolute : absoluteSource := by
  conic at bound

def squareSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to bound : wrappedSquare x ≤ t

#guard_error_fragments ["terminal conic validation is uncertified: constraint `bound`:"] in
assert_helper_atomic%
reformulation noWrappedSquare : squareSource := by
  conic

def exponentialSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to
      first : |cost 2 1 x| ≤ t
      bound : wrappedExp x ≤ t

#guard_error_fragments ["constraint `bound`:"] in
assert_helper_atomic%
reformulation noWrappedExponential : exponentialSource certificate noWrappedAlias := by
  conic at first
  conic at bound

def predicateSource :=
  problem (x t : ℝ)
    minimize cost 2 1 x
    subject to bound : wrappedPredicate x t

#guard_error_fragments ["terminal conic validation is uncertified: constraint `bound`:"] in
assert_helper_atomic%
reformulation noWrappedPredicate : predicateSource := by
  conic

-- Option changes take effect at the model command and do not escape its scope.
set_option morew.affine.maxExpansionSteps 0 in
#guard_error_fragments ["terminal conic validation is uncertified: objective:"] in
assert_helper_atomic%
reformulation helpersDisabled : minimum := by
  conic

reformulation helpersReenabled : minimum := by
  conic

example : IsConic helpersReenabled := helpersReenabled.isConic

end Boundaries

end
end MorewTest.Reformulation.AffineHelpers
