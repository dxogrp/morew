/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation

/-!
# Complete smooth-NLP reformulations

Terminal validation stores concrete scalar rows while preserving the comparison
presentation, objective values, and model-local binding identities. The examples
also exercise nonconvex objectives and continuation from a certified target.
-/

namespace MorewTest.Reformulation.TerminalNLP

open Morew
noncomputable section

-- Nonconvexity is independent of twice continuous differentiability.
def polynomial :=
  problem (x y : ℝ)
    minimize x * y - x ^ 4
    subject to
      grouped : (x ^ 2 ≤ y ∧ True) ∧ y ≤ 5
      equality : x * y = 1

reformulation polynomialTarget : polynomial := by
  nlp

example : GlobalEquivalence polynomial polynomialTarget := polynomialTarget.equivalence
example : NLP.Form polynomialTarget := polynomialTarget.nlpForm
example : IsSmoothNLP polynomialTarget := polynomialTarget.isSmoothNLP
example : polynomialTarget.nlpForm.data.toProblem = polynomialTarget :=
  polynomialTarget.nlpForm.represents
example : polynomialTarget.nlpForm.data.sense = .minimize := rfl
example : polynomialTarget.nlpForm.data.rowCount = 3 := rfl
example (x y : ℝ) : polynomialTarget.objective (x, y) = x * y - x ^ 4 := rfl
example (x y : ℝ) : polynomialTarget.feasible (x, y) ↔
    ((x ^ 2 ≤ y ∧ True) ∧ y ≤ 5) ∧ x * y = 1 := Iff.rfl
example (x y : ℝ) :
    (polynomialTarget.nlpForm.data.rows ⟨0, by decide⟩).residual (x, y) =
      x ^ 2 - y := rfl
example : (polynomialTarget.nlpForm.data.rows ⟨0, by decide⟩).bounds =
    NLP.Bounds.upperBound 0 := rfl
example : (polynomialTarget.nlpForm.data.rows ⟨2, by decide⟩).bounds =
    NLP.Bounds.fixed 0 := rfl

/--
info: problem (x y : ℝ)
  minimize x * y - x ^ 4
  subject to
    grouped : (x ^ 2 ≤ y ∧ True) ∧ y ≤ 5
    equality : x * y = 1
-/
#guard_msgs in
#printp polynomialTarget

def maximum :=
  problem (x : ℝ)
    maximize Real.log x - x ^ 2
    subject to
      domain : 1 ≤ x

reformulation maximumTarget : maximum := by
  nlp
example : Problem ℝ (OrderDual ℝ) := maximumTarget
example : maximumTarget.nlpForm.data.sense = .maximize := rfl
example (x : ℝ) : maximumTarget.objective x = Real.log x - x ^ 2 := rfl
example : maximumTarget.nlpForm.data.toProblem = maximumTarget :=
  maximumTarget.nlpForm.represents

run_cmd Lean.Elab.Command.liftTermElabM do
  let type := (← Lean.getConstInfo ``maximumTarget).type
  unless type.isAppOfArity ``Morew.Problem 2 &&
      type.getAppArgs[1]!.isAppOfArity ``OrderDual 1 do
    Lean.throwError "maximizing NLP target lost its explicit OrderDual annotation"
  let info ← Lean.getConstInfo ``polynomialTarget.isSmoothNLP
  let some value := info.value? (allowOpaque := true)
    | Lean.throwError "missing smooth-NLP property definition"
  unless (value.find? (·.isConstOf ``polynomialTarget.nlpForm)).isSome do
    Lean.throwError "the representability witness did not reference the named form"

def unconstrained := problem (x : ℝ) minimize Real.sin x
reformulation unconstrainedTarget : unconstrained := by
  nlp
example : unconstrainedTarget.nlpForm.data.rowCount = 0 := rfl

def allTrue := problem (_x : Fin 0 → ℝ) minimize (0 : ℝ) subject to trivial : True ∧ True
reformulation allTrueTarget : allTrue := by
  nlp
example : allTrueTarget.nlpForm.data.rowCount = 0 := rfl

-- Only groups needing exact lowering are split. Unaffected definitions and
-- repeated bodies retain their original identities rather than being guessed.
def localDefinitions :=
  problem (x y : ℝ)
    let first := x ^ 2
    let second := x ^ 2
    minimize first + second + y ^ 2
    subject to
      bound : |x| ≤ y ∧ y ≤ 4
      untouched : first ≤ second + 1

reformulation localTarget : localDefinitions := by
  nlp
example : GlobalEquivalence localDefinitions localTarget := localTarget.equivalence
example : localTarget.nlpForm.data.rowCount = 4 := rfl

/--
info: problem (x y : ℝ)
  let first := x ^ 2
  let second := x ^ 2
  minimize first + second + y ^ 2
  subject to
    bound_nlp_1 : x ≤ y
    bound_nlp_2 : -x ≤ y
    bound_nlp_3 : y ≤ 4
    untouched : first ≤ second + 1
-/
#guard_msgs in
#printp localTarget

reformulation continued : localTarget := by
  epigraph t at first
  nlp
example : GlobalEquivalence localTarget continued := continued.equivalence
example : IsSmoothNLP continued := continued.isSmoothNLP

reformulation targetedFirst : localDefinitions := by
  epigraph a at (|x|) in bound
  nlp at epigraph_a
  nlp
example : GlobalEquivalence localDefinitions targetedFirst := targetedFirst.equivalence
example : IsSmoothNLP targetedFirst := targetedFirst.isSmoothNLP

-- Terminal selection uses the existing direct-bound rules in source order.
def scalarRules :=
  problem (x y t : ℝ)
    minimize x * y
    subject to
      absolute : |x ^ 2 - y| ≤ t
      positive : (x ^ 3)⁺ ≤ t
      maximum : max (Real.sin x) (y ^ 2) ≤ t
      minimum : -t ≤ min (x * y) (Real.exp y)

reformulation scalarRulesTarget : scalarRules := by
  nlp
example : scalarRulesTarget.nlpForm.data.rowCount = 8 := rfl
example (x y t : ℝ) : scalarRulesTarget.feasible ((x, y), t) ↔
    x ^ 2 - y ≤ t ∧ -(x ^ 2 - y) ≤ t ∧ x ^ 3 ≤ t ∧ 0 ≤ t ∧
    Real.sin x ≤ t ∧ y ^ 2 ≤ t ∧ -t ≤ x * y ∧ -t ≤ Real.exp y := Iff.rfl

def oneLeafGroup :=
  problem (x : ℝ)
    minimize x ^ 2
    subject to
      bounds : True ∧ |x| ≤ 2 ∧ True

reformulation oneLeafTarget : oneLeafGroup := by
  nlp
example : oneLeafTarget.nlpForm.data.rowCount = 2 := rfl
example (x : ℝ) : oneLeafTarget.feasible x ↔ x ≤ 2 ∧ -x ≤ 2 := Iff.rfl

-- The earlier logarithm needs a guard exposed by the later exact rewrite.
def retryDomain :=
  problem (x y : ℝ)
    minimize Real.log x
    subject to
      earlier : |Real.log x| ≤ y
      later : 1 ≤ min x y

reformulation retryDomainTarget : retryDomain := by
  nlp
example : retryDomainTarget.nlpForm.data.rowCount = 4 := rfl
example : GlobalEquivalence retryDomain retryDomainTarget := retryDomainTarget.equivalence

namespace AllocatedNames

def source :=
  problem (v : Fin 2 → ℝ) (budget_aux : ℝ)
    let budget_aux_1 := budget_aux + 1
    minimize budget_aux_1 ^ 2
    subject to
      budget_nlp_1 : 1 ≤ budget_aux
      budget : ‖WithLp.toLp 1 v‖ ≤ budget_aux
      logarithm : Real.log budget_aux ≤ 5

reformulation target : source := by
  nlp
example : target.nlpForm.data.rowCount = 7 := rfl
example : IsSmoothNLP target := target.isSmoothNLP
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "missing terminal NLP presentation"
  unless view.binders.map (·.name.eraseMacroScopes) == #[`v, `budget_aux, `budget_aux_2] do
    Lean.throwError "terminal NLP auxiliary allocation ignored a local definition"
  unless view.constraints.map (·.name.eraseMacroScopes) ==
      #[`budget_nlp_1, `budget_nlp_1_1, `budget_nlp_2, `budget_nlp_3, `logarithm] do
    Lean.throwError "terminal NLP row allocation changed ordered labels"

end AllocatedNames

-- A literal source bound can be certified without changing its orientation.
def reversed := problem (x : ℝ) minimize x ^ 2 subject to lower : x ≥ 1
reformulation reversedTarget : reversed := by
  nlp
example (x : ℝ) : reversedTarget.feasible x ↔ x ≥ 1 := Iff.rfl
example (x : ℝ) : (reversedTarget.nlpForm.data.rows ⟨0, by decide⟩).residual x =
    x - 1 := rfl
example : (reversedTarget.nlpForm.data.rows ⟨0, by decide⟩).bounds =
    NLP.Bounds.lowerBound 0 := rfl

end
end MorewTest.Reformulation.TerminalNLP
