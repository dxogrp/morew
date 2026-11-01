/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Command
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Derived-constraint rejection and atomicity

The proof is checked against the complete current problem, before the new row
exists. Failed commands must discard earlier step helpers as well as outputs.
-/

namespace MorewTest.Reformulation.DeriveFailures

open Morew
noncomputable section

elab "assert_derive_atomic% " target:ident aliasName:ident " in " nested:command :
    command => do
  let before ← Lean.getEnv
  let namespaceName ← Lean.getCurrNamespace
  let target := namespaceName ++ target.getId
  let aliasName := namespaceName ++ aliasName.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed derivation changed declarations or certificate helpers"
  for name in #[target, target ++ `equivalence, aliasName] do
    if after.contains name then Lean.throwError m!"failed derivation emitted {name}"
    if (Morew.Syntax.getProblemView? after name).isSome then
      Lean.throwError m!"failed derivation registered presentation metadata for {name}"

def unrestricted := problem (x : ℝ) minimize x

def bounded :=
  problem (x : ℝ)
    minimize x
    subject to
      lower : -1 ≤ x
      upper : x ≤ 1

theorem selfBound : ∀ point, unrestricted.feasible point → point ≤ point := by
  intro point _
  exact le_refl point

#guard_error_fragments ["Type mismatch"] in
assert_derive_atomic% falseClaim falseClaimAlias in
reformulation falseClaim : bounded certificate falseClaimAlias := by
  derive stronger : 0 ≤ x using (fun _ feasible => feasible.1)

#guard_error_fragments ["a derived constraint must be a proposition"] in
assert_derive_atomic% nonProposition nonPropositionAlias in
reformulation nonProposition : bounded certificate nonPropositionAlias := by
  derive number : x using selfBound

#guard_error_fragments ["Unknown identifier", "missing"] in
assert_derive_atomic% unknownVariable unknownVariableAlias in
reformulation unknownVariable : bounded certificate unknownVariableAlias := by
  derive unknown : missing ≤ x using selfBound

#guard_error_fragments ["derived constraint proof", "unresolved metavariables"] in
assert_derive_atomic% unfinishedProof unfinishedProofAlias in
reformulation unfinishedProof : unrestricted certificate unfinishedProofAlias := by
  derive self : x ≤ x using (fun _ _ => ?_)

#guard_error_fragments ["Type mismatch"] in
assert_derive_atomic% noSelfEvidence noSelfEvidenceAlias in
reformulation noSelfEvidence : unrestricted certificate noSelfEvidenceAlias := by
  derive domain : 0 ≤ x using (fun _ feasible => feasible)

-- Neither the decision spelling nor the constraint label introduces a proof local.
#guard_error_fragments ["Unknown identifier", "x"] in
assert_derive_atomic% decisionLeak decisionLeakAlias in
reformulation decisionLeak : unrestricted certificate decisionLeakAlias := by
  derive self : x = x using (fun _ _ => Eq.refl x)

#guard_error_fragments ["Unknown identifier", "lower"] in
assert_derive_atomic% labelLeak labelLeakAlias in
reformulation labelLeak : bounded certificate labelLeakAlias := by
  derive repeated : -1 ≤ x using (fun _ _ => lower)

-- A theorem about the original scalar problem does not cover an introduced coordinate.
#guard_error_fragments ["Type mismatch"] in
assert_derive_atomic% staleProof staleProofAlias in
reformulation staleProof : unrestricted certificate staleProofAlias := by
  epigraph t
  derive self : x ≤ x using selfBound

#guard_error_fragments ["constraint name `lower` already exists"] in
assert_derive_atomic% existingLabel existingLabelAlias in
reformulation existingLabel : bounded certificate existingLabelAlias := by
  derive lower : x ≤ x using (fun point _ => le_refl point)

#guard_error_fragments ["constraint name `shared` already exists"] in
assert_derive_atomic% repeatedLabel repeatedLabelAlias in
reformulation repeatedLabel : unrestricted certificate repeatedLabelAlias := by
  derive shared : x ≤ x using selfBound
  derive shared : x = x using (fun point _ => Eq.refl point)

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_derive_atomic% epigraphFirst epigraphFirstAlias in
reformulation epigraphFirst : unrestricted certificate epigraphFirstAlias := by
  epigraph t as bound
  derive bound : x ≤ x using (fun point _ => le_refl point.1)

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_derive_atomic% deriveFirst deriveFirstAlias in
reformulation deriveFirst : unrestricted certificate deriveFirstAlias := by
  derive bound : x ≤ x using selfBound
  epigraph t as bound

def maximum := problem (x : ℝ) maximize x

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_derive_atomic% hypographFirst hypographFirstAlias in
reformulation hypographFirst : maximum certificate hypographFirstAlias := by
  hypograph t as bound
  derive bound : x ≤ x using (fun point _ => le_refl point.1)

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_derive_atomic% deriveBeforeHypograph deriveBeforeHypographAlias in
reformulation deriveBeforeHypograph : maximum certificate deriveBeforeHypographAlias := by
  derive bound : x = x using (fun point _ => Eq.refl point)
  hypograph t as bound

-- The predicate's actual operation instance must agree with its proof.
private abbrev reversedLE : LE ℝ := ⟨fun a b => b ≤ a⟩

theorem usualLower : ∀ point, bounded.feasible point → -1 ≤ point := by
  intro point feasible
  exact feasible.1

#guard_error_fragments ["Type mismatch"] in
assert_derive_atomic% changedOrder changedOrderAlias in
reformulation changedOrder : bounded certificate changedOrderAlias := by
  derive reversed : @LE.le ℝ reversedLE (-1) x using usualLower

private abbrev shiftedAdd : HAdd ℝ ℝ ℝ := ⟨fun a b => a + b + 1⟩

theorem usualAddition : ∀ point, unrestricted.feasible point → point + 0 = point := by
  intro point _
  exact add_zero point

#guard_error_fragments ["Type mismatch"] in
assert_derive_atomic% changedAddition changedAdditionAlias in
reformulation changedAddition : unrestricted certificate changedAdditionAlias := by
  derive shifted : @HAdd.hAdd ℝ ℝ ℝ shiftedAdd x 0 = x using usualAddition

-- Successful derivations and auxiliary introductions are all rolled back on a late error.
#guard_error_fragments ["Unknown identifier", "missingProof"] in
assert_derive_atomic% failedAfterDerive failedAfterDeriveAlias in
reformulation failedAfterDerive : unrestricted certificate failedAfterDeriveAlias := by
  derive self : x ≤ x using selfBound
  epigraph t
  derive later : t ≤ t using missingProof

def positive :=
  problem (x : ℝ)
    minimize Real.log x
    subject to domain : 0 < x

#guard_error_fragments ["Unknown identifier", "missingProof"] in
assert_derive_atomic% failedAfterSubstitution failedAfterSubstitutionAlias in
reformulation failedAfterSubstitution : positive
    certificate failedAfterSubstitutionAlias := by
  substitute x := Real.exp u
  derive self : u = u using missingProof

#guard_error_fragments ["terminal"] in
assert_derive_atomic% afterTerminal afterTerminalAlias in
reformulation afterTerminal : unrestricted certificate afterTerminalAlias := by
  conic
  derive self : x ≤ x using selfBound

-- General proved propositions are stored; a terminal consumer applies its own policy.
reformulation withDisequality : positive := by
  derive nonzero : x ≠ 0 using (by
    intro point feasible
    exact ne_of_gt feasible)

#guard_error_fragments ["disjunction"] in
assert_derive_atomic% unsupportedConic unsupportedConicAlias in
reformulation unsupportedConic : unrestricted certificate unsupportedConicAlias := by
  derive disjunction : x ≤ 0 ∨ 0 ≤ x using (fun point _ => le_total point 0)
  conic

#guard_error_fragments ["disjunction"] in
assert_derive_atomic% unsupportedNLP unsupportedNLPAlias in
reformulation unsupportedNLP : unrestricted certificate unsupportedNLPAlias := by
  derive disjunction : x ≤ 0 ∨ 0 ≤ x using (fun point _ => le_total point 0)
  nlp

-- Missing clauses are parser errors, not implicit proof search requests.
run_cmd do
  for input in #["derive bound : x ≤ x", "derive : x ≤ x using selfBound",
      "derive bound : x ≤ x using"] do
    match Lean.Parser.runParserCategory (← Lean.getEnv) `reformulationStep input with
    | .error _ => pure ()
    | .ok _ => Lean.throwError m!"malformed derive step parsed successfully: {input}"

-- Reusing a failed output name verifies recovery after declaration rollback.
reformulation failedAfterDerive : unrestricted certificate failedAfterDeriveAlias := by
  derive self : x ≤ x using selfBound

example : GlobalEquivalence unrestricted failedAfterDerive := failedAfterDeriveAlias

end
end MorewTest.Reformulation.DeriveFailures
