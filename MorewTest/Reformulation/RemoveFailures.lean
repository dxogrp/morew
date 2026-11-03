/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.Diagnostics
import MorewTest.Environment

/-! # Removal never uses the selected row, historical rows, or general search -/

namespace MorewTest.Reformulation.RemoveFailures

open Morew
noncomputable section

elab "assert_remove_atomic% " target:ident aliasName:ident " in " nested:command :
    command => do
  let before ← Lean.getEnv
  let namespaceName ← Lean.getCurrNamespace
  let target := namespaceName ++ target.getId
  let aliasName := namespaceName ++ aliasName.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed removal changed declarations or certificate helpers"
  for name in #[target, target ++ `equivalence, aliasName,
      target ++ `conicForm, target ++ `isConic,
      target ++ `nlpForm, target ++ `isSmoothNLP] do
    if after.contains name then Lean.throwError m!"failed removal emitted {name}"
    if (Morew.Syntax.getProblemView? after name).isSome ||
        (Morew.Syntax.getProblemDisplayView? after name).isSome ||
        (Morew.Syntax.getProblemPrintPresentation? after name).isSome then
      Lean.throwError m!"failed removal registered presentation metadata for {name}"

def bounded :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1
      relaxed : x ≤ 3

def duplicate :=
  problem (x : ℝ)
    minimize x
    subject to
      first : 0 ≤ x
      second : 0 ≤ x

def sole := problem (x : ℝ) minimize x subject to necessary : 0 ≤ x
def empty := problem (x : ℝ) minimize x

#guard_error_fragments ["unknown or stale constraint label `missing`"] in
assert_remove_atomic% unknown unknownAlias in
reformulation unknown : bounded certificate unknownAlias := by
  remove at missing

#guard_error_fragments ["unknown or stale constraint label `missing`"] in
assert_remove_atomic% noRows noRowsAlias in
reformulation noRows : empty certificate noRowsAlias := by
  remove at missing

#guard_error_fragments ["constraint", "necessary", "using"] in
assert_remove_atomic% soleNecessary soleNecessaryAlias in
reformulation soleNecessary : sole certificate soleNecessaryAlias := by
  remove at necessary

-- A feasible point violating the proposed removal exists; no fact about the
-- original feasible predicate can make the last remaining bound disappear.
#guard_error_fragments ["constraint", "second", "using"] in
assert_remove_atomic% circular circularAlias in
reformulation circular : duplicate certificate circularAlias := by
  remove at first
  remove at second

#guard_error_fragments ["constraint", "relaxed", "using"] in
assert_remove_atomic% noArithmetic noArithmeticAlias in
reformulation noArithmetic : bounded certificate noArithmeticAlias := by
  remove at relaxed

def simplifiable :=
  problem (x : ℝ)
    minimize x
    subject to selected : x + 0 = x

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% noSimpDatabase noSimpDatabaseAlias in
reformulation noSimpDatabase : simplifiable certificate noSimpDatabaseAlias := by
  remove at selected

def impossible :=
  problem (x : ℝ)
    minimize x
    subject to
      contradiction : False
      selected : 0 ≤ x

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% noExFalso noExFalsoAlias in
reformulation noExFalso : impossible certificate noExFalsoAlias := by
  remove at selected

def grouped :=
  problem (x : ℝ)
    minimize x
    subject to
      bounds : 0 ≤ x ∧ x ≤ 1
      selected : 0 ≤ x

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% noProjection noProjectionAlias in
reformulation noProjection : grouped certificate noProjectionAlias := by
  remove at selected

def split :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : 0 ≤ x
      upper : x ≤ 1
      selected : 0 ≤ x ∧ x ≤ 1

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% noReconstruction noReconstructionAlias in
reformulation noReconstruction : split certificate noReconstructionAlias := by
  remove at selected

-- Explicit evidence bypasses automatic success instead of silently falling back.
#guard_error_fragments ["Type mismatch"] in
assert_remove_atomic% wrongExplicit wrongExplicitAlias in
reformulation wrongExplicit : duplicate certificate wrongExplicitAlias := by
  remove at first using (fun _ _ => True.intro)

#guard_error_fragments ["Type mismatch"] in
assert_remove_atomic% noSelfEvidence noSelfEvidenceAlias in
reformulation noSelfEvidence : sole certificate noSelfEvidenceAlias := by
  remove at necessary using (fun _ hp => hp)

theorem originalEvidence : ∀ point, sole.feasible point → 0 ≤ point := by
  intro point hp
  exact hp

#guard_error_fragments ["Type mismatch"] in
assert_remove_atomic% staleEvidence staleEvidenceAlias in
reformulation staleEvidence : sole certificate staleEvidenceAlias := by
  remove at necessary using originalEvidence

#guard_error_fragments ["Unknown identifier", "x"] in
assert_remove_atomic% noBinderLeak noBinderLeakAlias in
reformulation noBinderLeak : duplicate certificate noBinderLeakAlias := by
  remove at first using (fun _ _ => le_refl x)

#guard_error_fragments ["Unknown identifier", "second"] in
assert_remove_atomic% noLabelLeak noLabelLeakAlias in
reformulation noLabelLeak : duplicate certificate noLabelLeakAlias := by
  remove at first using (fun _ _ => second)

#guard_error_fragments ["unknown or stale constraint label `first`"] in
assert_remove_atomic% staleSelected staleSelectedAlias in
reformulation staleSelected : duplicate certificate staleSelectedAlias := by
  remove at first
  remove at first

#guard_error_fragments ["unknown or stale constraint label `first`"] in
assert_remove_atomic% renamedSelected renamedSelectedAlias in
reformulation renamedSelected : duplicate certificate renamedSelectedAlias := by
  rename first to domain
  remove at first

def qualified :=
  problem (x : ℝ)
    minimize x
    subject to labels.cap : True

#guard_error_fragments ["unknown or stale constraint label `cap`"] in
assert_remove_atomic% exactLabel exactLabelAlias in
reformulation exactLabel : qualified certificate exactLabelAlias := by
  remove at cap

section
variable (threshold : ℝ) (hthreshold : 0 ≤ threshold)

def ambient := problem (x : ℝ) minimize x subject to selected : 0 ≤ threshold

-- Bounded automation intentionally ignores section hypotheses.
#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% ambientIgnored ambientIgnoredAlias in
reformulation ambientIgnored : (ambient threshold) certificate ambientIgnoredAlias := by
  remove at selected

reformulation ambientExplicit : (ambient threshold) := by
  remove at selected using (fun _ _ => hthreshold)

example (x : ℝ) : ambientExplicit.feasible x ↔ True := Iff.rfl
example : GlobalEquivalence (ambient threshold) ambientExplicit :=
  ambientExplicit.equivalence threshold hthreshold
end

private abbrev strictLE : LE ℝ := ⟨fun a b => a < b⟩
private abbrev reversedLT : LT ℝ := ⟨fun a b => b < a⟩
private abbrev shiftedPow : HPow ℝ Nat ℝ := ⟨fun a b => a ^ b - 1⟩
private abbrev negativeNorm : Norm ℝ := ⟨fun x => -|x|⟩

def changedOrder :=
  problem (x : ℝ)
    minimize x
    subject to selected : @LE.le ℝ strictLE x x

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% alteredReflexivity alteredReflexivityAlias in
reformulation alteredReflexivity : changedOrder certificate alteredReflexivityAlias := by
  remove at selected

def changedStrictOrder :=
  problem (x : ℝ)
    minimize x
    subject to selected : @LT.lt ℝ reversedLT 0 (Real.exp x)

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% alteredExponential alteredExponentialAlias in
reformulation alteredExponential : changedStrictOrder certificate alteredExponentialAlias := by
  remove at selected

def changedPower :=
  problem (x : ℝ)
    minimize x
    subject to selected : 0 ≤ @HPow.hPow ℝ Nat ℝ shiftedPow x 2

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% alteredSquare alteredSquareAlias in
reformulation alteredSquare : changedPower certificate alteredSquareAlias := by
  remove at selected

def changedNorm :=
  problem (x : ℝ)
    minimize x
    subject to
      usual : ‖x‖ ≤ 1
      selected : @Norm.norm ℝ negativeNorm x ≤ 1

#guard_error_fragments ["constraint", "selected", "using"] in
assert_remove_atomic% distinctNorms distinctNormsAlias in
reformulation distinctNorms : changedNorm certificate distinctNormsAlias := by
  remove at selected

run_cmd do
  for malformed in #["remove", "remove first", "remove at", "remove at *",
      "remove at first using", "remove at first, second"] do
    match Lean.Parser.runParserCategory (← Lean.getEnv) `reformulationStep malformed with
    | .error _ => pure ()
    | .ok _ => Lean.throwError "malformed removal syntax was accepted: {malformed}"

end
end MorewTest.Reformulation.RemoveFailures
