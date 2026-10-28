/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Reformulation
import MorewTest.Diagnostics
import MorewTest.Environment

/-!
# Smooth helper certification across reformulation commands

Expansion is temporary proof-construction work. Semantic expressions, printed
helper references, local binding identities, and exported artifact signatures
must continue to describe the original source. A later failure must roll back
an earlier successful helper-based rewrite.
-/

namespace MorewTest.Reformulation.SmoothHelpers

open Morew
noncomputable section

def smoothSquare (x : ℝ) : ℝ := x * x
def smoothShift (offset x : ℝ) : ℝ := smoothSquare x + offset

section
variable (offset : ℝ)

def source :=
  problem (x y : ℝ)
    let first := smoothSquare x
    let second := smoothSquare x
    minimize first + second + y ^ 2
    subject to
      bound : |smoothShift offset x| ≤ y
      untouched : first ≤ second + 1

reformulation target : (source offset) := by
  nlp

example : GlobalEquivalence (source offset) (target offset) := target.equivalence offset
example : NLP.Form (target offset) := target.nlpForm offset
example : IsSmoothNLP (target offset) := target.isSmoothNLP offset
example : (target.nlpForm offset).data.toProblem = target offset :=
  (target.nlpForm offset).represents
example : (target.nlpForm offset).data.rowCount = 3 := rfl
example (x y : ℝ) : (target offset).objective (x, y) =
    smoothSquare x + smoothSquare x + y ^ 2 := rfl
example (x y : ℝ) : (target offset).feasible (x, y) ↔
    smoothShift offset x ≤ y ∧ -smoothShift offset x ≤ y ∧
      smoothSquare x ≤ smoothSquare x + 1 := Iff.rfl
example (x y : ℝ) :
    ((target.nlpForm offset).data.rows ⟨0, by change 0 < 3; decide⟩).residual (x, y) =
      smoothShift offset x - y := rfl

/--
info: problem (x y : ℝ)
  let first := smoothSquare x
  let second := smoothSquare x
  minimize first + second + y ^ 2
  subject to
    bound_nlp_1 : smoothShift offset x ≤ y
    bound_nlp_2 : -smoothShift offset x ≤ y
    untouched : first ≤ second + 1
-/
#guard_msgs in
#printp target

-- Equal helper bodies must not make an occurrence of `first` select `second`.
reformulation continued : (target offset) := by
  epigraph t at first as square_bound
  nlp

example : GlobalEquivalence (target offset) (continued offset) := continued.equivalence offset
example : NLP.Form (continued offset) := continued.nlpForm offset
example (x y t : ℝ) : (continued offset).objective ((x, y), t) =
    t + smoothSquare x + y ^ 2 := rfl

/--
info: problem (x y t : ℝ)
  let first := smoothSquare x
  let second := smoothSquare x
  minimize t + second + y ^ 2
  subject to
    bound_nlp_1 : smoothShift offset x ≤ y
    bound_nlp_2 : -smoothShift offset x ≤ y
    untouched : first ≤ second + 1
    square_bound : first ≤ t
-/
#guard_msgs in
#printp continued

end

-- Certification must not add proof-only parameters or instances to the source
-- or to its emitted problem, equivalence, form, and representability witnesses.
example : ℝ → Problem (ℝ × ℝ) ℝ := source
example : ℝ → Problem (ℝ × ℝ) ℝ := target
example : ∀ offset, GlobalEquivalence (source offset) (target offset) := target.equivalence
example : ∀ offset, NLP.Form (target offset) := target.nlpForm
example : ∀ offset, IsSmoothNLP (target offset) := target.isSmoothNLP

run_cmd do
  for name in #[``source, ``target, ``continued] do
    let some view := Syntax.getProblemView? (← Lean.getEnv) name
      | Lean.throwError "missing smooth-helper presentation"
    unless view.definitions.map (·.name.eraseMacroScopes) == #[`first, `second] do
      Lean.throwError "smooth helper certification changed local-definition identities"

run_cmd Lean.Elab.Command.liftTermElabM do
  for name in #[``target, ``continued] do
    let info ← Lean.getConstInfo name
    let some value := info.value? (allowOpaque := true)
      | Lean.throwError "missing smooth-helper target definition"
    unless (value.find? (·.isConstOf ``smoothSquare)).isSome &&
        (value.find? (·.isConstOf ``smoothShift)).isSome do
      Lean.throwError "smooth helper certification expanded the emitted semantic definition"
  for name in #[``target.equivalence, ``target.nlpForm, ``target.isSmoothNLP,
      ``continued.equivalence, ``continued.nlpForm] do
    let info ← Lean.getConstInfo name
    let some value := info.value? (allowOpaque := true)
      | Lean.throwError "missing smooth-helper certificate"
    if value.hasMVar || value.hasSorry then
      Lean.throwError "smooth helper certification emitted incomplete evidence"
    Lean.Meta.checkWithKernel value

elab "assert_smooth_helper_atomic% " nested:command : command => do
  let before ← Lean.getEnv
  let `(command| reformulation $target:ident : $_source:ident
      $[certificate $_alias:ident]? := by $_steps:reformulationStep*) := nested
    | Lean.throwError "expected a reformulation command"
  let targetName := (← Lean.getCurrNamespace) ++ target.getId
  try Lean.Elab.Command.elabCommand nested catch error => Lean.Elab.logException error
  let after ← Lean.getEnv
  if let some name := MorewTest.newLocalDeclaration? before after then
    Lean.throwError m!"failed smooth helper conversion leaked declaration {name}"
  if (Syntax.getProblemView? before targetName).isNone &&
      (Syntax.getProblemView? after targetName).isSome then
    Lean.throwError "failed smooth helper conversion leaked presentation metadata"

def lateFailure :=
  problem (x t : ℝ)
    minimize smoothSquare x
    subject to
      first : |smoothShift 1 x| ≤ t
      later : x < 0

#guard_error_fragments ["constraint `later`"] in
assert_smooth_helper_atomic%
reformulation lateTarget : lateFailure certificate lateEquivalence := by
  nlp at first
  nlp

-- A nonzero depth limit permits the first rewrite but stops the nested helper
-- in the objective. Its diagnostic and all artifact rollback checks must survive.
def budgetFailure :=
  problem (x t : ℝ)
    minimize smoothShift 1 x
    subject to first : |smoothSquare x| ≤ t

set_option morew.smooth.maxExpansionDepth 1 in
#guard_error_fragments ["morew.smooth.maxExpansionDepth", "limit 1"] in
assert_smooth_helper_atomic%
reformulation budgetTarget : budgetFailure certificate budgetEquivalence := by
  nlp at first
  nlp

def hiddenMagnitude (x : ℝ) : ℝ := |x|

def bodyFailure :=
  problem (x t : ℝ)
    minimize hiddenMagnitude x
    subject to first : |smoothSquare x| ≤ t

#guard_error_fragments ["objective", "not globally smooth"] in
assert_smooth_helper_atomic%
reformulation bodyTarget : bodyFailure certificate bodyEquivalence := by
  nlp at first
  nlp

end
end MorewTest.Reformulation.SmoothHelpers
