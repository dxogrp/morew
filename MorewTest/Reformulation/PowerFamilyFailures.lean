/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics
import MorewTest.Environment

/-! # Finite power-lift boundaries and atomic failures -/

namespace MorewTest.Reformulation.PowerFamilyFailures

open Morew
open scoped ENNReal
noncomputable section

elab "assert_power_family_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  if let some name := MorewTest.newLocalDeclaration? before (← Lean.getEnv) then
    Lean.throwError m!"failed finite power rewrite leaked declaration {name}"

def normSource (p : ℝ≥0∞) :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound : ‖WithLp.toLp p x‖ ≤ t

#guard_error_fragments ["bound", "required"] in
reformulation belowOne : (normSource (1 / 2)) := by
  conic at bound

section
variable (p : ℝ≥0∞) (hp : 1 ≤ p.toReal)
include hp in
#guard_error_fragments ["bound", "required"] in
reformulation unresolvedExponent : (normSource p) := by
  conic
end

def meanSource (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    maximize t
    subject to
      domain : 0 ≤ x
      mean : t ≤ Fn.geoMean x

section
variable (n : ℕ)
#guard_error_fragments ["mean", "nonempty dimension"] in
reformulation missingDimension : (meanSource n) := by
  conic at mean
end

#guard_error_fragments ["mean", "nonempty dimension"] in
reformulation emptyMean : (meanSource 0) := by
  conic at mean

def inverseSource (n : ℕ) :=
  problem (x : Fin n → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : (fun _ => 1) ≤ x
      inverse : Fn.invProd x ≤ t

#guard_error_fragments ["inverse", "nonempty dimension"] in
reformulation emptyInverse : (inverseSource 0) := by
  conic at inverse

def missingDomain :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    maximize t
    subject to mean : t ≤ Fn.geoMean x

#guard_error_fragments ["mean", "coordinatewise nonnegative"] in
reformulation meanMissingDomain : missingDomain := by
  conic

def zeroMargin :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : 0 ≤ x
      inverse : Fn.invProd x ≤ t

#guard_error_fragments ["inverse", "coordinatewise positive"] in
reformulation inverseMissingPositiveDomain : zeroMargin := by
  conic

def reversedNorm :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    maximize t
    subject to bound : t ≤ ‖WithLp.toLp 3 x‖

#guard_error_fragments ["bound", "conic rule"] in
reformulation normWrongPolarity : reversedNorm := by
  conic at bound

def reversedMean :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : 0 ≤ x
      mean : Fn.geoMean x ≤ t

#guard_error_fragments ["mean", "conic rule"] in
reformulation meanWrongPolarity : reversedMean := by
  conic at mean

def reversedInverse :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    maximize t
    subject to
      domain : (fun _ => 1) ≤ x
      inverse : t ≤ Fn.invProd x

#guard_error_fragments ["inverse", "conic rule"] in
reformulation inverseWrongPolarity : reversedInverse := by
  conic at inverse

private opaque nonNativeNorm : Norm (WithLp (3 : ℝ≥0∞) (Fin 2 → ℝ)) := ⟨fun _ => 0⟩

def alteredNorm :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to bound :
      @Norm.norm (WithLp (3 : ℝ≥0∞) (Fin 2 → ℝ)) nonNativeNorm (WithLp.toLp 3 x) ≤ t

#guard_error_fragments ["bound", "instance"] in
assert_power_family_atomic%
reformulation alteredNormRejected : alteredNorm := by
  conic at bound

#guard_error_fragments ["bound", "instance"] in
assert_power_family_atomic%
reformulation alteredNormExplicitRejected : alteredNorm := by
  conic at bound using Conic.Power.normEpigraph

-- The same source succeeds with L1; selecting the inapplicable power rule must
-- fail instead of falling back to that registered representation.
#guard_error_fragments ["bound", "required"] in
assert_power_family_atomic%
reformulation explicitPowerAtOne : (normSource 1) := by
  conic at bound using Conic.Power.normEpigraph

reformulation automaticAtOne : (normSource 1) := by conic
example : GlobalEquivalence (normSource 1) automaticAtOne := automaticAtOne.equivalence
example : IsConic automaticAtOne := automaticAtOne.isConic

assert_not_exists inverseWrongPolarity inverseWrongPolarity.equivalence
  alteredNormRejected alteredNormRejected.equivalence
  alteredNormExplicitRejected alteredNormExplicitRejected.equivalence
  explicitPowerAtOne explicitPowerAtOne.equivalence

def nonmonotone :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      domain : (fun _ => 1) ≤ x
      inverse : Real.sin (Fn.invProd x) ≤ t

#guard_error_fragments ["inverse", "conic rule"] in
reformulation nonmonotoneRejected : nonmonotone := by
  conic at inverse

#guard_error_fragments ["missing"] in
reformulation unknownLabel : (normSource 3) := by
  conic at missing

def lateFailure :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize t
    subject to
      bound : ‖WithLp.toLp 3 x‖ ≤ t
      invalid : Real.sin (x 0) ≤ t

#guard_error_fragments ["invalid"] in
assert_power_family_atomic%
reformulation lateTargeted : lateFailure certificate lateAlias := by
  conic at bound
  conic

#guard_error_fragments ["invalid"] in
assert_power_family_atomic%
reformulation lateTerminal : lateFailure := by
  conic

assert_not_exists lateTargeted lateAlias lateTargeted.equivalence lateTargeted.conicForm
  lateTerminal lateTerminal.equivalence lateTerminal.conicForm

-- Explicit objective-bound names still reject collisions with original decisions.
def nameCollision :=
  problem (x : Fin 2 → ℝ) (t : ℝ)
    minimize ‖WithLp.toLp 3 x‖
    subject to lower : 0 ≤ t

#guard_error_fragments ["t"] in
assert_power_family_atomic%
reformulation duplicateAuxiliary : nameCollision := by
  epigraph t
  conic

-- Automatic names freshen both the auxiliary and generated row labels while
-- retaining the pre-existing coordinate and constraint in their original slots.
def automaticNameCollision :=
  problem (x : Fin 2 → ℝ) (t : ℝ) (bound_aux : Fin 2 → ℝ)
    minimize t
    subject to
      bound_conic_1 : bound_aux = x
      bound : ‖WithLp.toLp 3 x‖ ≤ t

reformulation freshNames : automaticNameCollision := by
  conic at bound

example : GlobalEquivalence automaticNameCollision freshNames := freshNames.equivalence
example (x old r : Fin 2 → ℝ) (t : ℝ) :
    freshNames.objective (((x, t), old), r) = t := rfl
example (x old r : Fin 2 → ℝ) (t : ℝ) :
    freshNames.feasible (((x, t), old), r) ↔
      old = x ∧ 0 ≤ t ∧ (∑ i, r i) ≤ t ∧
        ∀ i, (r i, t, x i) ∈ Morew.Conic.Cone.powerSet (1 / 3 : ℝ) := Iff.rfl

run_cmd do
  let some view := Morew.Syntax.getProblemView? (← Lean.getEnv) ``freshNames
    | Lean.throwError "missing finite power auxiliary collision presentation"
  unless view.binders.size == 4 &&
      view.binders[2]!.name.eraseMacroScopes == `bound_aux &&
      view.binders[3]!.name.eraseMacroScopes != `bound_aux do
    Lean.throwError "power lift did not preserve and freshen the auxiliary names"
  let names := view.constraints.map (·.name.eraseMacroScopes)
  unless names.size == 4 && names[0]! == `bound_conic_1 &&
      names.toList.eraseDups.length == names.size do
    Lean.throwError "power lift changed an existing label or duplicated a generated label"

reformulation recovered : (normSource 3) := by conic
example : GlobalEquivalence (normSource 3) recovered := recovered.equivalence
example : IsConic recovered := recovered.isConic

end
end MorewTest.Reformulation.PowerFamilyFailures
