/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Basic
import MorewTest.DiagnosticsSupport
import MorewTest.Environment

/-! # Restrictions must certify the complete current problem -/

namespace MorewTest.Reformulation.RestrictFailures

open Morew
noncomputable section

elab "assert_restrict_atomic% " target:ident aliasName:ident " in " nested:command :
    command => do
  let before ← Lean.getEnv
  let namespaceName ← Lean.getCurrNamespace
  let target := namespaceName ++ target.getId
  let aliasName := namespaceName ++ aliasName.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed restriction changed declarations or certificate helpers"
  for name in #[target, target ++ `equivalence, aliasName] do
    if after.contains name || (Morew.Syntax.getProblemView? after name).isSome then
      Lean.throwError m!"failed restriction retained output or metadata for {name}"

def free := problem (x : ℝ) minimize x
def squareLine := problem (x : ℝ) minimize x ^ 2
def flat := problem (_x : ℝ) minimize (0 : ℝ)
def maximum := problem (x : ℝ) maximize x
def tagged := problem (x : ℝ) minimize x subject to kept : True

def trueRepair {X V : Type*} [Preorder V] (p : Problem X V) :
    GlobalImprovement p (p.addConstraint (fun _ => True)) where
  map point := ⟨point.1, point.2, True.intro⟩
  objective_le _ := le_rfl

def constantRepair (value : ℝ) :
    GlobalImprovement flat (flat.addConstraint (fun x => x = value)) where
  map _ := ⟨value, True.intro, rfl⟩
  objective_le _ := le_rfl

def zeroRepair :
    GlobalImprovement squareLine (squareLine.addConstraint (fun x => 0 ≤ x)) where
  map _ := ⟨0, True.intro, le_rfl⟩
  objective_le point := by simpa [squareLine] using sq_nonneg point.1

-- This improvement is valid only in the opposite objective order.
def increasingRepair :
    GlobalImprovement free.orderDual (free.orderDual.addConstraint (fun _ => True)) where
  map point := ⟨point.1 + 1, True.intro, True.intro⟩
  objective_le point := show point.1 ≤ point.1 + 1 from
    le_add_of_nonneg_right zero_le_one

#guard_error_fragments ["Type mismatch"] in
assert_restrict_atomic% wrongCondition wrongConditionAlias in
reformulation wrongCondition : free certificate wrongConditionAlias := by
  restrict condition : False using trueRepair free

#guard_error_fragments ["Type mismatch"] in
assert_restrict_atomic% wrongSource wrongSourceAlias in
reformulation wrongSource : free certificate wrongSourceAlias := by
  restrict tag : True using trueRepair squareLine

#guard_error_fragments ["Type mismatch"] in
assert_restrict_atomic% wrongOrder wrongOrderAlias in
reformulation wrongOrder : free certificate wrongOrderAlias := by
  restrict tag : True using increasingRepair

#guard_error_fragments ["restriction", "must be a proposition"] in
assert_restrict_atomic% nonProposition nonPropositionAlias in
reformulation nonProposition : free certificate nonPropositionAlias := by
  restrict number : x using trueRepair free

#guard_error_fragments ["Unknown identifier", "missing"] in
assert_restrict_atomic% unknownVariable unknownVariableAlias in
reformulation unknownVariable : free certificate unknownVariableAlias := by
  restrict condition : missing ≤ x using trueRepair free

-- Decision bindings and presentation labels are not available in the certificate.
#guard_error_fragments ["Unknown identifier", "_x"] in
assert_restrict_atomic% decisionLeak decisionLeakAlias in
reformulation decisionLeak : flat certificate decisionLeakAlias := by
  restrict fixed : _x = 0 using constantRepair _x

#guard_error_fragments ["Unknown identifier", "fixed"] in
assert_restrict_atomic% labelLeak labelLeakAlias in
reformulation labelLeak : flat certificate labelLeakAlias := by
  restrict fixed : _x = 0 using fixed

#guard_error_fragments ["Type mismatch"] in
assert_restrict_atomic% staleAfterEpigraph staleAfterEpigraphAlias in
reformulation staleAfterEpigraph : free certificate staleAfterEpigraphAlias := by
  epigraph t
  restrict tag : True using trueRepair free

def nonnegative := problem (x : ℝ) minimize x subject to domain : 0 ≤ x

reformulation normalizedSquare : nonnegative := by
  substitute x := u ^ 2

-- A raw helper cannot silently match a separately emitted, normalized target.
-- The successful imported tests supply an explicit checked simplification.
#guard_error_fragments ["Type mismatch"] in
assert_restrict_atomic% rawAfterCheckpoint rawAfterCheckpointAlias in
reformulation rawAfterCheckpoint : normalizedSquare certificate rawAfterCheckpointAlias := by
  restrict tag : True using trueRepair (nonnegative.pullback (fun u : ℝ => u ^ 2))

-- Each repair is valid for flat alone, but the second one violates the first row.
#guard_error_fragments ["Type mismatch"] in
assert_restrict_atomic% losesEarlierRestriction losesEarlierRestrictionAlias in
reformulation losesEarlierRestriction : flat certificate losesEarlierRestrictionAlias := by
  restrict zero : _x = 0 using constantRepair 0
  restrict one : _x = 1 using constantRepair 1

#guard_error_fragments ["constraint name `shared` already exists"] in
assert_restrict_atomic% repeatedLabel repeatedLabelAlias in
reformulation repeatedLabel : free certificate repeatedLabelAlias := by
  restrict shared : True using trueRepair free
  restrict shared : True using trueRepair free

#guard_error_fragments ["constraint name `kept` already exists"] in
assert_restrict_atomic% existingLabel existingLabelAlias in
reformulation existingLabel : tagged certificate existingLabelAlias := by
  restrict kept : True using trueRepair tagged

#guard_error_fragments ["constraint name `shared` already exists"] in
assert_restrict_atomic% deriveFirst deriveFirstAlias in
reformulation deriveFirst : free certificate deriveFirstAlias := by
  derive shared : True using (fun _ _ => True.intro)
  restrict shared : True using trueRepair free

#guard_error_fragments ["constraint name `shared` already exists"] in
assert_restrict_atomic% restrictFirst restrictFirstAlias in
reformulation restrictFirst : free certificate restrictFirstAlias := by
  restrict shared : True using trueRepair free
  derive shared : True using (fun _ _ => True.intro)

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_restrict_atomic% epigraphFirst epigraphFirstAlias in
reformulation epigraphFirst : free certificate epigraphFirstAlias := by
  epigraph t as bound
  restrict bound : True using trueRepair free

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_restrict_atomic% restrictBeforeEpigraph restrictBeforeEpigraphAlias in
reformulation restrictBeforeEpigraph : free certificate restrictBeforeEpigraphAlias := by
  restrict bound : True using trueRepair free
  epigraph t as bound

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_restrict_atomic% hypographFirst hypographFirstAlias in
reformulation hypographFirst : maximum certificate hypographFirstAlias := by
  hypograph t as bound
  restrict bound : True using trueRepair (V := OrderDual ℝ) maximum

#guard_error_fragments ["constraint name `bound` already exists"] in
assert_restrict_atomic% restrictBeforeHypograph restrictBeforeHypographAlias in
reformulation restrictBeforeHypograph : maximum certificate restrictBeforeHypographAlias := by
  restrict bound : True using trueRepair (V := OrderDual ℝ) maximum
  hypograph t as bound

section
variable (cap : ℝ)

#guard_error_fragments ["decision variable `cap` conflicts with a source parameter"] in
assert_restrict_atomic% operandCollision operandCollisionAlias in
reformulation operandCollision : free certificate operandCollisionAlias := by
  restrict operand : cap = cap using {
    map := fun point => ⟨point.1, point.2, rfl⟩
    objective_le := fun _ => le_rfl }
  epigraph cap
end

private abbrev reversedLE : LE ℝ := ⟨fun a b => b ≤ a⟩

#guard_error_fragments ["Type mismatch"] in
assert_restrict_atomic% changedOrder changedOrderAlias in
reformulation changedOrder : squareLine certificate changedOrderAlias := by
  restrict reversed : @LE.le ℝ reversedLE 0 x using zeroRepair

-- Square coverage cannot be inferred before a certified source restriction.
#guard_error_fragments ["substitution", "0 ≤"] in
assert_restrict_atomic% uncoveredSquare uncoveredSquareAlias in
reformulation uncoveredSquare : squareLine certificate uncoveredSquareAlias := by
  substitute x := u ^ 2

#guard_error_fragments ["Unknown identifier", "x"] in
assert_restrict_atomic% removedBinder removedBinderAlias in
reformulation removedBinder : squareLine certificate removedBinderAlias := by
  restrict domain : 0 ≤ x using zeroRepair
  substitute x := u ^ 2
  restrict obsolete : x = 0 using constantRepair 0

#guard_error_fragments ["Unknown identifier", "missingCertificate"] in
assert_restrict_atomic% failedLate failedLateAlias in
reformulation failedLate : squareLine certificate failedLateAlias := by
  restrict domain : 0 ≤ x using zeroRepair
  substitute x := u ^ 2
  epigraph t
  restrict later : True using missingCertificate

run_cmd do
  for input in #["restrict branch : 0 ≤ x", "restrict : True using trueRepair free",
      "restrict branch : True using", "restrict 17 : True using trueRepair free"] do
    match Lean.Parser.runParserCategory (← Lean.getEnv) `reformulationStep input with
    | .error _ => pure ()
    | .ok _ => Lean.throwError m!"malformed restriction parsed successfully: {input}"

-- Reusing a rolled-back target and alias must succeed.
reformulation failedLate : squareLine certificate failedLateAlias := by
  restrict domain : 0 ≤ x using zeroRepair

example : GlobalEquivalence squareLine failedLate := failedLateAlias

end
end MorewTest.Reformulation.RestrictFailures
