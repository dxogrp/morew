/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation.Command
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Objective occurrence bounds in decreasing contexts

The selected function's bound direction follows its surrounding checked context.
Negation, subtraction, and fixed negative coefficients can therefore use a
hypograph inside minimization or an epigraph inside maximization.
-/

namespace MorewTest.Reformulation.NegatedOccurrence

open Morew
noncomputable section

def logSource :=
  problem (x : ℝ)
    minimize -Real.log x
    subject to
      domain : 1 ≤ x
      cap : x ≤ 3

reformulation logBound : logSource := by
  hypograph value at (Real.log x) as rewardBound

example : GlobalEquivalence logSource logBound := logBound.equivalence
example (x value : ℝ) : logBound.objective (x, value) = -value := rfl
example (x value : ℝ) : logBound.feasible (x, value) ↔
    1 ≤ x ∧ x ≤ 3 ∧ value ≤ Real.log x := Iff.rfl

/--
info: problem (x value : ℝ)
  minimize -value
  subject to
    domain : 1 ≤ x
    cap : x ≤ 3
    rewardBound : value ≤ Real.log x
-/
#guard_msgs in
#printp logBound

reformulation logConic : logBound := by conic

example : GlobalEquivalence logSource logConic :=
  logBound.equivalence.trans logConic.equivalence
example : IsConic logConic := logConic.isConic
example : logConic.conicForm.data.toProblem = logConic := logConic.conicForm.represents

def absSource := problem (x : ℝ) maximize -|x|

reformulation absBound : absSource := by
  epigraph magnitude at (|x|)

example : GlobalEquivalence absSource absBound := absBound.equivalence
example (x magnitude : ℝ) : absBound.objective (x, magnitude) = -magnitude := rfl
example (x magnitude : ℝ) : absBound.feasible (x, magnitude) ↔ |x| ≤ magnitude := Iff.rfl

reformulation absConic : absBound := by conic

example : IsConic absConic := absConic.isConic
example : absConic.conicForm.data.sense = .maximize := rfl

def compoundSource :=
  problem (x y : ℝ)
    minimize -(Real.log x + min y 1)
    subject to domain : 1 ≤ x

-- Two selected bounds suffice; no whole-objective bound is introduced.
reformulation compoundBound : compoundSource := by
  hypograph a at (Real.log x)
  hypograph b at (min y 1)

example (x y a b : ℝ) : compoundBound.objective (((x, y), a), b) = -(a + b) := rfl
example (x y a b : ℝ) : compoundBound.feasible (((x, y), a), b) ↔
    1 ≤ x ∧ a ≤ Real.log x ∧ b ≤ min y 1 := Iff.rfl

reformulation compoundConic : compoundBound := by conic

example : GlobalEquivalence compoundSource compoundConic :=
  compoundBound.equivalence.trans compoundConic.equivalence
example : IsConic compoundConic := compoundConic.isConic
example : compoundConic.conicForm.data.rowCount = 4 := rfl

def nestedSource := problem (x : ℝ) minimize - - -Real.log x

reformulation nestedBound : nestedSource := by
  hypograph t at (Real.log x)

example (x t : ℝ) : nestedBound.objective (x, t) = - - -t := rfl
example (x t : ℝ) : nestedBound.feasible (x, t) ↔ t ≤ Real.log x := Iff.rfl

def doubleSource := problem (x : ℝ) minimize - -|x|

reformulation doubleBound : doubleSource := by
  epigraph t at (|x|)

example (x t : ℝ) : doubleBound.objective (x, t) = - -t := rfl

def subtractSource := problem (x : ℝ) minimize x - Real.log x

reformulation subtractBound : subtractSource := by
  hypograph t at (Real.log x)

example (x t : ℝ) : subtractBound.objective (x, t) = x - t := rfl

def coefficientSource := problem (x : ℝ) minimize (-2) * Real.log x

reformulation coefficientBound : coefficientSource := by
  hypograph t at (Real.log x)

example (x t : ℝ) : coefficientBound.objective (x, t) = (-2) * t := rfl

section Parameter

variable (c : ℝ) (hc : c ≤ 0)

def parameterSource := problem (x : ℝ) minimize c * Real.log x

reformulation parameterBound : (parameterSource c) := by
  hypograph t at (Real.log x)

example (x t : ℝ) : (parameterBound c).objective (x, t) = c * t := rfl
example : GlobalEquivalence (parameterSource c) (parameterBound c) :=
  parameterBound.equivalence c hc

end Parameter

def hiddenNegative (x : ℝ) : ℝ := -x

def explicitSource := problem (x : ℝ) minimize hiddenNegative (Real.log x)

-- An explicit certificate can justify the selected direction even when the
-- context's named mathematical head stays opaque to automatic analysis.
reformulation explicitBound : explicitSource := by
  hypograph t at (Real.log x) using (by
    refine { atValue := ?_, backward := ?_ }
    · intro x
      rfl
    · intro x _ t bound
      change t ≤ Real.log x at bound
      change -Real.log x ≤ -t
      exact neg_le_neg bound)

example : GlobalEquivalence explicitSource explicitBound := explicitBound.equivalence

#guard_error_fragments ["cannot certify bound context"] in
reformulation wrongLogDirection : logSource := by
  epigraph t at (Real.log x)

#guard_error_fragments ["cannot certify bound context"] in
reformulation wrongAbsDirection : absSource := by
  hypograph t at (|x|)

section MissingSign

variable (c : ℝ)

#guard_error_fragments ["cannot certify bound context"] in
reformulation missingCoefficientSign : (parameterSource c) := by
  hypograph t at (Real.log x)

end MissingSign

#guard_error_fragments ["cannot certify bound context"] in
reformulation opaqueWithoutEvidence : explicitSource := by
  hypograph t at (Real.log x)

-- Bare objective bounds retain their objective-sense requirements.
#guard_error_fragments ["`hypograph` is not valid for a minimization problem"] in
reformulation wrongBareLog : logSource := by hypograph t

#guard_error_fragments ["`epigraph` is not valid for a maximization problem"] in
reformulation wrongBareAbs : absSource := by epigraph t

elab "assert_negated_occurrence_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  unless MorewTest.sameLocalDeclarationNames before after do
    Lean.throwError "failed negated occurrence lift changed declarations"

#guard_error_fragments ["cannot certify bound context"] in
assert_negated_occurrence_atomic%
reformulation failedChain : compoundSource := by
  hypograph a at (Real.log x)
  epigraph b at (min y 1)

run_cmd do
  let env ← Lean.getEnv
  for name in #[`wrongLogDirection, `wrongAbsDirection, `missingCoefficientSign,
      `opaqueWithoutEvidence, `wrongBareLog, `wrongBareAbs, `failedChain] do
    let name := `MorewTest.Reformulation.NegatedOccurrence ++ name
    if env.contains name || (Morew.Syntax.getProblemView? env name).isSome then
      Lean.throwError "failed negated occurrence lift retained its declaration or presentation"

end
end MorewTest.Reformulation.NegatedOccurrence
