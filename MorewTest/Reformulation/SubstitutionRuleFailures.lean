/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.Substitution.Registry.Source
import MorewTest.DiagnosticsSupport
import MorewTest.Environment

/-!
# Coordinate substitution rejection and atomicity

Failures preserve declarations and presentation metadata, including when an
earlier successful substitution has already allocated a coverage helper.
-/

namespace MorewTest.Reformulation.SubstitutionRuleFailures

open Morew
noncomputable section

elab "assert_substitution_atomic% " target:ident aliasName:ident " in " nested:command :
    command => do
  let before ← Lean.getEnv
  let namespaceName ← Lean.getCurrNamespace
  let target := namespaceName ++ target.getId
  let aliasName := namespaceName ++ aliasName.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed substitution changed declarations or coverage helpers"
  for name in #[target, target ++ `equiv, aliasName] do
    if after.contains name then Lean.throwError m!"failed substitution emitted {name}"
    if (Morew.Syntax.getProblemView? after name).isSome then
      Lean.throwError m!"failed substitution registered presentation metadata for {name}"

def unrestricted := problem (x : ℝ) minimize x

def nonnegative :=
  problem (x : ℝ)
    maximize x
    subject to domain : 0 ≤ x

def positive :=
  problem (x : ℝ)
    minimize Real.log x
    subject to domain : 0 < x

#guard_error_fragments ["substitution of `x`", "fully certified"] in
assert_substitution_atomic% repeatedCoordinate repeatedCoordinateAlias in
reformulation repeatedCoordinate : unrestricted certificate repeatedCoordinateAlias := by
  substitute x := u + u

#guard_error_fragments ["substitution of `x`", "fully certified"] in
assert_substitution_atomic% composedAffine composedAffineAlias in
reformulation composedAffine : unrestricted certificate composedAffineAlias := by
  substitute x := 2 * (u + 1)

#guard_error_fragments ["substitution of `x`", "coverage"] in
assert_substitution_atomic% zeroSlope zeroSlopeAlias in
reformulation zeroSlope : unrestricted certificate zeroSlopeAlias := by
  substitute x := 0 * u

#guard_error_fragments ["substitution of `x`", "coverage"] in
assert_substitution_atomic% missingSquare missingSquareAlias in
reformulation missingSquare : unrestricted certificate missingSquareAlias := by
  substitute x := u ^ 2

#guard_error_fragments ["substitution of `x`", "coverage"] in
assert_substitution_atomic% missingExponential missingExponentialAlias in
reformulation missingExponential : nonnegative certificate missingExponentialAlias := by
  substitute x := Real.exp u

-- A wrong explicit rule never falls back to an otherwise applicable square rule.
#guard_error_fragments ["substitution of `x`", "does not match"] in
assert_substitution_atomic% wrongNamed wrongNamedAlias in
reformulation wrongNamed : nonnegative certificate wrongNamedAlias := by
  substitute x := u ^ 2 via Morew.Substitution.exp

#guard_error_fragments ["Type mismatch", "CoordinateParameterization"] in
assert_substitution_atomic% wrongApplied wrongAppliedAlias in
reformulation wrongApplied : nonnegative certificate wrongAppliedAlias := by
  substitute x := u ^ 2 via (Morew.Substitution.exp (R := Unit))

#guard_error_fragments ["Application type mismatch"] in
assert_substitution_atomic% wrongNewType wrongNewTypeAlias in
reformulation wrongNewType : unrestricted certificate wrongNewTypeAlias := by
  substitute x := Nat.succ u

private abbrev changedNeg : Neg ℝ := ⟨fun u => u + 1⟩
private abbrev changedPower : HPow ℝ ℕ ℝ := ⟨fun u _ => u⟩

#guard_error_fragments ["substitution of `x`", "operation instance"] in
assert_substitution_atomic% wrongNegation wrongNegationAlias in
reformulation wrongNegation : unrestricted certificate wrongNegationAlias := by
  substitute x := @Neg.neg ℝ changedNeg u

#guard_error_fragments ["substitution of `x`", "operation instance"] in
assert_substitution_atomic% wrongPower wrongPowerAlias in
reformulation wrongPower : nonnegative certificate wrongPowerAlias := by
  substitute x := @HPow.hPow ℝ ℕ ℝ changedPower u 2

-- Proof parameters are independent premises, even when the problem carries
-- their proposition as a source constraint. Put feasible-only guards in range.
def guardedShift {R : Type*} (c : ℝ) (_h : 0 < c) :
    CoordinateParameterization (fun (_ : R) (u : ℝ) => u + c) :=
  Morew.Substitution.addRight (fun _ => c)

def parameterDomain (c : ℝ) :=
  problem (x : ℝ)
    minimize x
    subject to coefficient_domain : 0 < c

section
variable (c : ℝ)

#guard_error_fragments ["substitution of `x`", "independent premises"] in
assert_substitution_atomic% missingPremise missingPremiseAlias in
reformulation missingPremise : (parameterDomain c) certificate missingPremiseAlias := by
  substitute x := u + c via guardedShift

end

def unresolvedShape {R : Type*} (_shape : ℕ) :
    CoordinateParameterization (fun (_ : R) (u : ℝ) => u ^ 2) :=
  Morew.Substitution.square

#guard_error_fragments ["substitution of `x`", "unresolved parameters"] in
assert_substitution_atomic% missingShape missingShapeAlias in
reformulation missingShape : nonnegative certificate missingShapeAlias := by
  substitute x := u ^ 2 via unresolvedShape

-- Distinct imported and local declarations remain ambiguous in sorted order.
def duplicateSquare {R : Type*} :
    CoordinateParameterization (fun (_ : R) (u : ℝ) => u ^ 2) :=
  Morew.Substitution.square

def squareCoverage : FeasibleSurjection nonnegative (fun u : ℝ => u ^ 2) where
  preimage point := Real.sqrt point.1
  rightInverse point := Real.sq_sqrt point.2

section
attribute [local morew_substitute] duplicateSquare

#guard_error_fragments ["ambiguous coordinate parameterizations",
  "Morew.Substitution.square, MorewTest.Reformulation.SubstitutionRuleFailures.duplicateSquare",
  "via"] in
assert_substitution_atomic% ambiguous ambiguousAlias in
reformulation ambiguous : nonnegative certificate ambiguousAlias := by
  substitute x := u ^ 2

reformulation explicitSquare : nonnegative := by
  substitute x := u ^ 2 via duplicateSquare

-- Whole-problem certificates bypass automatic ambiguity entirely.
reformulation manualSquare : nonnegative := by
  substitute x := u ^ 2 using squareCoverage

example : GlobalEquiv nonnegative explicitSquare := explicitSquare.equiv
example : GlobalEquiv nonnegative manualSquare := manualSquare.equiv

end

open MorewTest.Substitution.Registry.Source in
#guard_error_fragments ["substitution of `x`", "does not match"] in
assert_substitution_atomic% wrongImported wrongImportedAlias in
reformulation wrongImported : unrestricted certificate wrongImportedAlias := by
  substitute x := u + 1 via shiftRule

-- A successful first step creates an auxiliary coverage declaration. A later
-- failure must discard it together with the target, equivalence, and alias.
#guard_error_fragments ["substitution of `u`", "coverage"] in
assert_substitution_atomic% failedAfterSquare failedAfterSquareAlias in
reformulation failedAfterSquare : nonnegative certificate failedAfterSquareAlias := by
  substitute x := u ^ 2
  substitute u := Real.exp v

#guard_error_fragments ["substitution of `u`", "fully certified"] in
assert_substitution_atomic% failedAfterExponential failedAfterExponentialAlias in
reformulation failedAfterExponential : positive certificate failedAfterExponentialAlias := by
  substitute x := Real.exp u
  substitute u := v + v

-- Parser rejection happens before command elaboration, so test the complete
-- input directly rather than letting a trailing token escape #guard_msgs.
#guard_msgs in
run_cmd do
  for input in #["substitute x := u ^ 2 via Morew.Substitution.square",
      "substitute x := u ^ 2 using squareCoverage"] do
    match Lean.Parser.runParserCategory (← Lean.getEnv) `reformulationStep input with
    | .ok _ => pure ()
    | .error message => Lean.throwError m!"valid substitution syntax rejected: {message}"
  let input := "substitute x := u ^ 2 via Morew.Substitution.square using squareCoverage"
  match Lean.Parser.runParserCategory (← Lean.getEnv) `reformulationStep input with
  | .ok _ => Lean.throwError "substitution accepted both via and using"
  | .error _ => pure ()
  let input := "substitute x := u ^ 2 using squareCoverage via Morew.Substitution.square"
  match Lean.Parser.runParserCategory (← Lean.getEnv) `reformulationStep input with
  | .ok _ => Lean.throwError "substitution accepted both using and via"
  | .error _ => pure ()

end
end MorewTest.Reformulation.SubstitutionRuleFailures
