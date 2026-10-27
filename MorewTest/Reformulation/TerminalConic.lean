/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Complete conic reformulations

Terminal conversion preserves conic groups, lowers nonlinear leaves in place,
and writes affine memberships with exact structural data for the final target.
-/

namespace MorewTest.Reformulation.TerminalConic

open Morew Morew.Conic
noncomputable section

def linear :=
  problem (x y : ℝ)
    minimize x + y
    subject to
      bounds : 0 ≤ x ∧ True ∧ y ≤ 5
      equal : x = y

reformulation linearTarget : linear := by
  conic

example : GlobalEquivalence linear linearTarget := linearTarget.equivalence
example : Conic.Form linearTarget := linearTarget.conicForm
example : IsConic linearTarget := linearTarget.isConic
example : linearTarget.conicForm.data.toProblem = linearTarget :=
  linearTarget.conicForm.represents
example : linearTarget.conicForm.data.sense = .minimize := rfl
example : linearTarget.conicForm.data.rowCount = 3 := rfl
example (x y : ℝ) :
    (linearTarget.conicForm.data.constraints ⟨0, by decide⟩).Holds (x, y) ↔ 0 ≤ x := by
  change 0 ≤ x - 0 ↔ 0 ≤ x
  rw [sub_zero]
example (x y : ℝ) :
    (linearTarget.conicForm.data.constraints ⟨2, by decide⟩).Holds (x, y) ↔ x = y := by
  change x - y = 0 ↔ x = y
  exact sub_eq_zero

/--
info: problem (x y : ℝ)
  minimize x + y
  subject to
    bounds : x ∈ ℝ₊ ∧ True ∧ 5 - y ∈ ℝ₊
    equal : x - y ∈ ({0} : Set ℝ)
-/
#guard_msgs in
#printp linearTarget

def unconstrained := problem (x : ℝ) minimize x
reformulation unconstrainedTarget : unconstrained := by
  conic
example : unconstrainedTarget.conicForm.data.rowCount = 0 := rfl
example : unconstrainedTarget.conicForm.data.toProblem = unconstrainedTarget :=
  unconstrainedTarget.conicForm.represents

def allTrue := problem (_x : Fin 0 → ℝ) minimize (0 : ℝ) subject to trivial : True ∧ True
reformulation allTrueTarget : allTrue := by
  conic
example : allTrueTarget.conicForm.data.rowCount = 0 := rfl

def maximum :=
  problem (x t : ℝ)
    maximize t
    subject to
      quadratic : x ^ 2 ≤ t
      upper : t ≤ 10

reformulation maximumTarget : maximum := by
  conic
example : Problem (ℝ × ℝ) (OrderDual ℝ) := maximumTarget
example : maximumTarget.conicForm.data.sense = .maximize := rfl
example : maximumTarget.conicForm.data.toProblem = maximumTarget := maximumTarget.conicForm.represents

run_cmd Lean.Elab.Command.liftTermElabM do
  let type := (← Lean.getConstInfo ``maximumTarget).type
  unless type.isAppOfArity ``Morew.Problem 2 &&
      type.getAppArgs[1]!.isAppOfArity ``OrderDual 1 do
    throwError "maximizing target lost its explicit OrderDual annotation"
  let info ← Lean.getConstInfo ``linearTarget.isConic
  let some value := info.value? (allowOpaque := true) | throwError "missing property definition"
  unless (value.find? (·.isConstOf ``linearTarget.conicForm)).isSome do
    throwError "the property did not reference the named form"

def grouped :=
  problem (x y t : ℝ)
    minimize t
    subject to
      first : x = y
      bounds : |x| ≤ t ∧ y ≤ 1
      domainLog : 1 ≤ x ∧ t ≤ Real.log x
      last : t ≤ 10

reformulation groupedTarget : grouped := by
  conic

/--
info: problem (x y t : ℝ)
  minimize t
  subject to
    first : x - y ∈ ({0} : Set ℝ)
    bounds_conic_1 : t - x ∈ ℝ₊
    bounds_conic_2 : t - -x ∈ ℝ₊
    bounds_conic_3 : 1 - y ∈ ℝ₊
    domainLog_conic_1 : x - 1 ∈ ℝ₊
    domainLog_conic_2 : (t, 1, x) ∈ EXP
    last : 10 - t ∈ ℝ₊
-/
#guard_msgs in
#printp groupedTarget

example : groupedTarget.conicForm.data.rowCount = 7 := rfl

def deferredMargin :=
  problem (x y t : ℝ)
    minimize t
    subject to
      logarithm : t ≤ Real.log x
      domain : 1 ≤ min x y

reformulation deferredTarget : deferredMargin := by
  conic
example : IsConic deferredTarget := deferredTarget.isConic

def mixed :=
  problem (x : ℝ) (v : Fin 2 → ℝ) (z : EuclideanSpace ℝ (Fin 1)) (t : ℝ)
    minimize t
    subject to
      polyhedral : |x| ≤ t
      euclidean : ‖z‖ ≤ t
      quadratic : (∑ i, v i ^ 2) ≤ t
      exponential : Real.exp x ≤ t

reformulation mixedTarget : mixed := by
  conic at polyhedral
  conic
example : mixedTarget.conicForm.data.rowCount = 5 := rfl
example : IsConic mixedTarget := mixedTarget.isConic

def collisions :=
  problem (x t loss_aux : ℝ)
    minimize t
    subject to
      loss_conic_1 : 0 ≤ loss_aux
      loss : Fn.softplus x ≤ t ∧ Fn.softplus (-x) ≤ t
      last : t ≤ 10

reformulation collisionsTarget : collisions := by
  conic
example : collisionsTarget.conicForm.data.rowCount = 6 := rfl

/--
info: problem (x t loss_aux : ℝ) (loss_aux_1 loss_aux_2 : Fin 2 → ℝ)
  minimize t
  subject to
    loss_conic_1 : loss_aux ∈ ℝ₊
    loss_conic_1_1 : ∀ (i : Fin 2), (![0, x] i - t, 1, loss_aux_1 i) ∈ EXP
    loss_conic_2 : 1 - ∑ i, loss_aux_1 i ∈ ℝ₊
    loss_conic_3 : ∀ (i : Fin 2), (![0, -x] i - t, 1, loss_aux_2 i) ∈ EXP
    loss_conic_4 : 1 - ∑ i, loss_aux_2 i ∈ ℝ₊
    last : 10 - t ∈ ℝ₊
-/
#guard_msgs in
#printp collisionsTarget

def logSquared :=
  problem (x : ℝ)
    minimize (Real.log x) ^ 2
    subject to positive : 0 < x

reformulation logSquaredTarget : logSquared := by
  substitute x := Real.exp u
  epigraph t
  conic
example : IsConic logSquaredTarget := logSquaredTarget.isConic

reformulation continued : logSquaredTarget := by
  epigraph value as objectiveBound
  conic
example : GlobalEquivalence logSquared continued :=
  logSquaredTarget.equivalence.trans continued.equivalence

def logMaximum :=
  problem (x : ℝ)
    maximize Real.log x
    subject to margin : 1 ≤ x

reformulation logMaximumTarget : logMaximum := by
  hypograph t
  conic
example : logMaximumTarget.conicForm.data.sense = .maximize := rfl

-- Both sides have rule heads, but are constants, so the affine row is retained.
def constants :=
  problem (x : ℝ)
    minimize x
    subject to
      overlap : Real.exp 0 ≤ Real.log 2
      fallback : |2| ≤ min x (x + 1)
reformulation constantsTarget : constants := by
  conic
example : constantsTarget.conicForm.data.rowCount = 3 := rfl

def named :=
  problem (x t : ℝ)
    minimize t
    subject to
      Bounds.loss : |x| ≤ t
      «loss bound» : x ^ 2 ≤ t
      final : t ≤ 5

-- Declaration names and presentation labels belong to separate namespaces.
def loss_conic_1 : Nat := 17
reformulation namedTarget : named := by
  conic
run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``namedTarget
    | Lean.throwError "missing terminal presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`loss_conic_1, `loss_conic_2, Lean.Name.mkSimple "loss bound_conic_1", `final] do
    Lean.throwError "terminal generated names lost qualified or escaped label stems"

-- Macro scopes are ignored for allocation while decoded labels stay readable.
macro "terminal_named_source%" : term =>
  `(problem (x t : ℝ) minimize t subject to generated : |x| ≤ t)
def macroSource := terminal_named_source%
reformulation macroTarget : macroSource := by
  conic
run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``macroTarget
    | Lean.throwError "missing macro-generated terminal presentation"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`generated_conic_1, `generated_conic_2] do
    Lean.throwError "terminal names retained macro scopes"

namespace FiniteInstances

class Parameter where
  Index : Type
  equiv : Fin 2 ≃ Index
  coeff : Index → ℝ

variable [Parameter]

/- The only finite-index evidence occurs inside the constraint's dot product.
Terminal planning must retain it while validating the constant objective,
lowering the nonlinear row, and emitting reusable form artifacts. -/
def source :=
  problem (x : Parameter.Index → ℝ)
    minimize (0 : ℝ)
    subject to
      bound : |@dotProduct Parameter.Index ℝ
        (Fintype.ofEquiv (Fin 2) Parameter.equiv) _ _ Parameter.coeff x| ≤ 1

reformulation automaticTarget : source := by
  conic

reformulation selectedTarget : source := by
  conic at bound
  conic

def auxiliarySource :=
  problem (x : Parameter.Index → ℝ)
    minimize (0 : ℝ)
    subject to
      bound : |@dotProduct Parameter.Index ℝ
        (Fintype.ofEquiv (Fin 2) Parameter.equiv) _ _ Parameter.coeff x| ≤ 1
      loss : Fn.softplus (@dotProduct Parameter.Index ℝ
        (Fintype.ofEquiv (Fin 2) Parameter.equiv) _ _ Parameter.coeff x) ≤ 2

reformulation auxiliaryTarget : auxiliarySource := by
  conic

example : GlobalEquivalence source automaticTarget := automaticTarget.equivalence
example : GlobalEquivalence source selectedTarget := selectedTarget.equivalence
example : GlobalEquivalence auxiliarySource auxiliaryTarget := auxiliaryTarget.equivalence

-- Only finiteness is recovered from source expressions. For ordinary field
-- notation, install the same canonical enumeration used by the stored forms.
local instance : Finite Parameter.Index := by
  let := Fintype.ofEquiv (Fin 2) Parameter.equiv
  infer_instance
local instance : Fintype Parameter.Index := Fintype.ofFinite Parameter.Index

example : automaticTarget.conicForm.data.rowCount = 2 := rfl
example : selectedTarget.conicForm.data.rowCount = 2 := rfl
example : auxiliaryTarget.conicForm.data.rowCount = 4 := rfl
example : automaticTarget.conicForm.data.toProblem = automaticTarget :=
  automaticTarget.conicForm.represents
example : selectedTarget.conicForm.data.toProblem = selectedTarget :=
  selectedTarget.conicForm.represents

example : Conic.Form automaticTarget := automaticTarget.conicForm
example : IsConic selectedTarget := selectedTarget.isConic
example : IsConic auxiliaryTarget := auxiliaryTarget.isConic

example (x : Parameter.Index → ℝ) :
    letI := Fintype.ofEquiv (Fin 2) Parameter.equiv
    automaticTarget.feasible x ↔
      1 - Parameter.coeff ⬝ᵥ x ∈ ℝ₊ ∧ 1 - -(Parameter.coeff ⬝ᵥ x) ∈ ℝ₊ := Iff.rfl
example (x : Parameter.Index → ℝ) :
    letI := Fintype.ofEquiv (Fin 2) Parameter.equiv
    selectedTarget.feasible x ↔
      1 - Parameter.coeff ⬝ᵥ x ∈ ℝ₊ ∧ 1 - -(Parameter.coeff ⬝ᵥ x) ∈ ℝ₊ := Iff.rfl

end FiniteInstances

namespace AliasedFiniteIndex

def IndexAlias := Fin 2

local instance : Finite IndexAlias := by
  change Finite (Fin 2)
  infer_instance
local instance : Fintype IndexAlias := Fintype.ofFinite IndexAlias

def first : IndexAlias := (0 : Fin 2)

def source :=
  problem (x : IndexAlias → ℝ)
    minimize x first
    subject to
      upper : x first ≤ 1

reformulation target : source := by
  conic

-- The exported form retains the index spelling required by its stored norm.
example : target.conicForm.data.rowCount = 1 := rfl
example : target.conicForm.data.toProblem = target := target.conicForm.represents
example : Conic.Form target := target.conicForm
example : IsConic target := target.isConic

end AliasedFiniteIndex

end
end MorewTest.Reformulation.TerminalConic
