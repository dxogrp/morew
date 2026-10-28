/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics
import MorewTest.Environment
import MorewTest.Reformulation.Registry.Source

/-!
# Exact auxiliary rewrites under retained constraints

The original rows supply a representation's domain condition. Its generated
rows may then introduce auxiliaries, but cannot justify that condition themselves.
-/

namespace MorewTest.Reformulation.ContextualRewrite

open Morew
noncomputable section

def positiveLogEpigraph :
    EpigraphRepresentation (fun x : {x : ℝ // 0 < x} => Real.log x.1) where
  Auxiliary := ℝ
  target x t u := x.1 = Real.exp u ∧ u ≤ t
  source_iff_exists x t := by
    constructor
    · intro h
      exact ⟨Real.log x.1, (Real.exp_log x.2).symm, h⟩
    · rintro ⟨u, hx, hu⟩
      simpa only [hx, Real.log_exp] using hu

def logSource :=
  problem (x t : ℝ)
    let value := Real.log x
    minimize t
    subject to
      positive : 1 ≤ x
      bound : value ≤ t
      after : t ≤ 10

reformulation targetedLog : logSource := by
  nlp at bound using positiveLogEpigraph

example : GlobalEquivalence logSource targetedLog := targetedLog.equivalence
example (x t u : ℝ) : targetedLog.feasible ((x, t), u) ↔
    1 ≤ x ∧ x = Real.exp u ∧ u ≤ t ∧ t ≤ 10 := Iff.rfl

-- A later script reuses the contextual step's presentation and equivalence.
reformulation terminalLog : targetedLog := by
  nlp

example : NLP.Form terminalLog := terminalLog.nlpForm
example : terminalLog.nlpForm.data.toProblem = terminalLog := terminalLog.nlpForm.represents
example : terminalLog.nlpForm.data.sense = .minimize := rfl

def guardedAbs (x : ℝ) : ℝ := |x|

@[morew_conic, morew_nlp]
def nonnegativeAbsEpigraph :
    EpigraphRepresentation (fun x : {x : ℝ // 0 ≤ x} => guardedAbs x.1) where
  Auxiliary := ℝ
  target x t u := u = x.1 ∧ u ≤ t
  source_iff_exists x t := by
    simp only [guardedAbs, abs_of_nonneg x.2, exists_eq_left]

def absSource :=
  problem (x t : ℝ)
    let magnitude := guardedAbs x
    minimize t
    subject to
      before : 0 ≤ x
      bound : magnitude ≤ t
      after : t ≤ 10

reformulation targetedConic : absSource := by
  conic at bound

reformulation targetedNLP : absSource := by
  nlp at bound

example : GlobalEquivalence absSource targetedConic := targetedConic.equivalence
example : GlobalEquivalence absSource targetedNLP := targetedNLP.equivalence
example (x t u : ℝ) : targetedConic.objective ((x, t), u) = t := rfl
example (x t u : ℝ) : targetedNLP.objective ((x, t), u) = t := rfl
example (x t u : ℝ) : targetedConic.feasible ((x, t), u) ↔
    0 ≤ x ∧ u = x ∧ u ≤ t ∧ t ≤ 10 := Iff.rfl
example (x t u : ℝ) : targetedNLP.feasible ((x, t), u) ↔
    0 ≤ x ∧ u = x ∧ u ≤ t ∧ t ≤ 10 := Iff.rfl

/--
info: problem (x t bound_aux : ℝ)
  let magnitude := guardedAbs x
  minimize t
  subject to
    before : 0 ≤ x
    bound_conic_1 : bound_aux = x
    bound_conic_2 : bound_aux ≤ t
    after : t ≤ 10
-/
#guard_msgs in
#printp targetedConic

-- A named nonsmooth helper forces both terminals to discover the guarded rule.
reformulation terminalConic : absSource := by
  conic

reformulation terminalNLP : absSource := by
  nlp

example : GlobalEquivalence absSource terminalConic := terminalConic.equivalence
example : GlobalEquivalence absSource terminalNLP := terminalNLP.equivalence
example : terminalConic.conicForm.data.toProblem = terminalConic :=
  terminalConic.conicForm.represents
example : terminalNLP.nlpForm.data.toProblem = terminalNLP := terminalNLP.nlpForm.represents
example : terminalConic.conicForm.data.rowCount = 4 := rfl
example : terminalNLP.nlpForm.data.rowCount = 4 := rfl

-- The second conditional rewrite must rebase the first auxiliary and every
-- retained row onto a further product, including already-certified rows.
def twoBounds :=
  problem (x t s : ℝ)
    minimize t + 2 * s
    subject to
      nonnegative : 0 ≤ x
      first : guardedAbs x ≤ t
      second : guardedAbs x ≤ s

reformulation twoConic : twoBounds := by
  conic

reformulation twoNLP : twoBounds := by
  nlp

example : Problem ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) ℝ := twoConic
example : Problem ((((ℝ × ℝ) × ℝ) × ℝ) × ℝ) ℝ := twoNLP
example (x t s u v : ℝ) : twoConic.objective ((((x, t), s), u), v) = t + 2 * s := rfl
example (x t s u v : ℝ) : twoNLP.objective ((((x, t), s), u), v) = t + 2 * s := rfl
example (x t s u v : ℝ) : twoNLP.feasible ((((x, t), s), u), v) ↔
    0 ≤ x ∧ u = x ∧ u ≤ t ∧ v = x ∧ v ≤ s := Iff.rfl
example : GlobalEquivalence twoBounds twoConic := twoConic.equivalence
example : GlobalEquivalence twoBounds twoNLP := twoNLP.equivalence
example : Conic.Form twoConic := twoConic.conicForm
example : NLP.Form twoNLP := twoNLP.nlpForm
example : twoConic.conicForm.data.toProblem = twoConic := twoConic.conicForm.represents
example : twoNLP.nlpForm.data.toProblem = twoNLP := twoNLP.nlpForm.represents
example : twoConic.conicForm.data.rowCount = 5 := rfl
example : twoNLP.nlpForm.data.rowCount = 5 := rfl

namespace Imported

def nonnegativeShiftedAbs (center : ℝ) (hc : center ≤ 0) :
    EpigraphRepresentation
      (fun x : {x : ℝ // 0 ≤ x} => Registry.Source.shiftedAbs center x.1) where
  Auxiliary := ℝ
  target x t u := u = x.1 - center ∧ u ≤ t
  source_iff_exists x t := by
    have h : 0 ≤ x.1 - center := sub_nonneg.mpr (le_trans hc x.2)
    simp only [Registry.Source.shiftedAbs, abs_of_nonneg h, exists_eq_left]

variable (center : ℝ) (hc : center ≤ 0)

-- The imported applied family keeps its original parameter and local definition.
-- The separate hypothesis is needed only by the equivalence certificate.
reformulation conicTarget : (Registry.Source.source center) := by
  conic at bound using (nonnegativeShiftedAbs center hc)
  conic

reformulation nlpTarget : (Registry.Source.source center) := by
  nlp at bound using (nonnegativeShiftedAbs center hc)
  nlp

example : GlobalEquivalence (Registry.Source.source center) (conicTarget center) :=
  conicTarget.equivalence center hc
example : GlobalEquivalence (Registry.Source.source center) (nlpTarget center) :=
  nlpTarget.equivalence center hc
example : Conic.Form (conicTarget center) := conicTarget.conicForm center
example : NLP.Form (nlpTarget center) := nlpTarget.nlpForm center
example : (conicTarget.conicForm center).data.toProblem = conicTarget center :=
  (conicTarget.conicForm center).represents
example : (nlpTarget.nlpForm center).data.toProblem = nlpTarget center :=
  (nlpTarget.nlpForm center).represents
example (x t u : ℝ) : (nlpTarget center).feasible ((x, t), u) ↔
    0 ≤ x ∧ u = x - center ∧ u ≤ t ∧ t ≤ 10 := Iff.rfl

end Imported

def maxAbsSource :=
  problem (x t : ℝ)
    maximize -t
    subject to
      bound : guardedAbs x ≤ t
      nonnegative : 0 ≤ x

-- Retained evidence may occur after the selected row.
reformulation maxConic : maxAbsSource := by
  conic

reformulation maxNLP : maxAbsSource := by
  nlp

example : Problem ((ℝ × ℝ) × ℝ) (OrderDual ℝ) := maxConic
example : Problem ((ℝ × ℝ) × ℝ) (OrderDual ℝ) := maxNLP
example : maxConic.conicForm.data.sense = .maximize := rfl
example : maxNLP.nlpForm.data.sense = .maximize := rfl

reformulation continued : targetedNLP := by
  epigraph objectiveBound
  conic

example : GlobalEquivalence targetedNLP continued := continued.equivalence
example : IsConic continued := continued.isConic

-- Unit remains the representation of an absent auxiliary decision variable.
def nonnegativeAbsUnit :
    EpigraphRepresentation (fun x : {x : ℝ // 0 ≤ x} => guardedAbs x.1) where
  Auxiliary := Unit
  target x t _ := x.1 ≤ t
  source_iff_exists x t := by
    simp only [guardedAbs, abs_of_nonneg x.2, exists_const]

reformulation unitConic : absSource := by
  conic at bound using nonnegativeAbsUnit
  conic

reformulation unitNLP : absSource := by
  nlp at bound using nonnegativeAbsUnit
  nlp

example : Problem (ℝ × ℝ) ℝ := unitConic
example : Problem (ℝ × ℝ) ℝ := unitNLP
example : unitConic.conicForm.data.rowCount = 3 := rfl
example : unitNLP.nlpForm.data.rowCount = 3 := rfl

elab "assert_contextual_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let `(command| reformulation $target:ident : $_source:ident
      $[certificate $_alias:ident]? := by $_steps:reformulationStep*) := nested
    | Lean.throwError "expected a reformulation command"
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed contextual rewrite changed local declarations"
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed contextual rewrite leaked presentation metadata"

def missingGuard :=
  problem (x t : ℝ)
    minimize t
    subject to bound : guardedAbs x ≤ t

#guard_error_fragments ["constraint `bound`", "missing nonnegative constant margin"] in
assert_contextual_atomic%
reformulation missingConic : missingGuard := by
  conic at bound using nonnegativeAbsEpigraph

#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
assert_contextual_atomic%
reformulation missingNLP : missingGuard := by
  nlp at bound using nonnegativeAbsEpigraph

-- Using the selected guard to discharge itself would erase its restriction.
def selectedGuardLift : ExactConstraintLift (fun x : {x : ℝ // 0 ≤ x} => 0 ≤ x.1) where
  Auxiliary := ℝ
  target x u := u = x.1
  source_iff_exists x := ⟨fun _ => ⟨x.1, rfl⟩, fun _ => x.2⟩

def selectedGuard := problem (x : ℝ) minimize x subject to bound : 0 ≤ x

def retainedGuard :=
  problem (x : ℝ)
    minimize x
    subject to
      retained : 1 ≤ x
      bound : 0 ≤ x

-- Parentheses select a concrete exact-lift value rather than declaration lookup.
reformulation concreteConic : retainedGuard := by
  conic at bound using (selectedGuardLift)

reformulation concreteNLP : retainedGuard := by
  nlp at bound using (selectedGuardLift)

example : GlobalEquivalence retainedGuard concreteConic := concreteConic.equivalence
example : GlobalEquivalence retainedGuard concreteNLP := concreteNLP.equivalence
example (x u : ℝ) : concreteConic.feasible (x, u) ↔ 1 ≤ x ∧ u = x := Iff.rfl
example (x u : ℝ) : concreteNLP.feasible (x, u) ↔ 1 ≤ x ∧ u = x := Iff.rfl

#guard_error_fragments ["constraint `bound`", "missing nonnegative constant margin"] in
assert_contextual_atomic%
reformulation selectedOnlyConic : selectedGuard := by
  conic at bound using selectedGuardLift

#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
assert_contextual_atomic%
reformulation selectedOnlyNLP : selectedGuard := by
  nlp at bound using selectedGuardLift

def generatedGuardEpigraph :
    EpigraphRepresentation (fun x : {x : ℝ // 0 ≤ x} => guardedAbs x.1) where
  Auxiliary := ℝ
  target x t u := 0 ≤ x.1 ∧ u = x.1 ∧ u ≤ t
  source_iff_exists x t := by
    simp only [guardedAbs, abs_of_nonneg x.2, x.2, true_and, exists_eq_left]

#guard_error_fragments ["constraint `bound`", "missing nonnegative constant margin"] in
assert_contextual_atomic%
reformulation generatedOnlyConic : missingGuard := by
  conic at bound using generatedGuardEpigraph

#guard_error_fragments ["constraint `bound`", "missing retained premise"] in
assert_contextual_atomic%
reformulation generatedOnlyNLP : missingGuard := by
  nlp at bound using generatedGuardEpigraph

-- A failure after the auxiliary step rolls back its generated declarations too.
#guard_error_fragments ["constraint `after`", "does not match"] in
assert_contextual_atomic%
reformulation lateFailure : absSource certificate lateFailureAlias := by
  nlp at bound
  conic at after using nonnegativeAbsEpigraph

section Ambiguous

attribute [local morew_conic] nonnegativeAbsUnit
attribute [local morew_nlp] nonnegativeAbsUnit

#guard_error_fragments ["ambiguous exact conic rules", "nonnegativeAbsEpigraph",
  "nonnegativeAbsUnit", "using"] in
assert_contextual_atomic%
reformulation ambiguousConic : absSource := by
  conic at bound

#guard_error_fragments ["ambiguous exact NLP rules", "nonnegativeAbsEpigraph",
  "nonnegativeAbsUnit", "using"] in
assert_contextual_atomic%
reformulation ambiguousNLP : absSource := by
  nlp at bound

reformulation explicitConic : absSource := by
  conic at bound using nonnegativeAbsEpigraph
  conic

reformulation explicitNLP : absSource := by
  nlp at bound using nonnegativeAbsEpigraph
  nlp

example : IsConic explicitConic := explicitConic.isConic
example : IsSmoothNLP explicitNLP := explicitNLP.isSmoothNLP

end Ambiguous

end
end MorewTest.Reformulation.ContextualRewrite
