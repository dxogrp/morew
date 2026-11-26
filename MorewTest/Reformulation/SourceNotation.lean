/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Basic

/-!
# Source notation through reformulations

Readable presentations retain source occurrences while exact replay and
equivalence certificates continue to refer to the checked expressions.
-/

@[expose] public section

namespace MorewTest.Reformulation.SourceNotation

open Morew Real
noncomputable section

def minExp (a : ℝ) :=
  problem (x : ℝ)
    let cost := exp x
    minimize cost
    subject to lower : a ≤ x

section

variable (a : ℝ)

reformulation epiMinExp : (minExp a) := by
  epigraph t as epiBound

example : GlobalEquiv (minExp a) (epiMinExp a) := epiMinExp.equiv a
example (x t : ℝ) : (epiMinExp a).objective (x, t) = t := rfl
example (x t : ℝ) : (epiMinExp a).feasible (x, t) ↔
    a ≤ x ∧ Real.exp x ≤ t := Iff.rfl

end

/--
info: problem (x : ℝ)
  let cost := exp x
  minimize cost
  subject to
    lower : a ≤ x
-/
#guard_msgs in
#printp minExp

/--
info: problem (x t : ℝ)
  let cost := exp x
  minimize t
  subject to
    lower : a ≤ x
    epiBound : cost ≤ t
-/
#guard_msgs in
#printp epiMinExp

/--
info: problem (x t : ℝ)
  let cost := exp x
  minimize t
  subject to
    lower : a ≤ x
    epiBound : cost ≤ t
-/
#guard_msgs in
set_option pp.proofs true in
#printp epiMinExp

-- Equal values retain the spelling and identity of each source occurrence.
def allFields :=
  problem (x : ℝ)
    let first := exp x
    let second := Real.exp x
    minimize first + second + exp x
    subject to cap : exp x ≤ 10

def shiftCoverage : FeasibleSurjection allFields (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

reformulation shifted : allFields := by
  substitute x := u + 1 using shiftCoverage

example : GlobalEquiv allFields shifted := shifted.equiv
example (u : ℝ) : shifted.objective u =
    Real.exp (u + 1) + Real.exp (u + 1) + Real.exp (u + 1) := rfl
example (u : ℝ) : shifted.feasible u ↔ Real.exp (u + 1) ≤ 10 := Iff.rfl

/--
info: problem (u : ℝ)
  let first := exp (u + 1)
  let second := Real.exp (u + 1)
  minimize first + second + exp (u + 1)
  subject to
    cap : exp (u + 1) ≤ 10
-/
#guard_msgs in
#printp shifted

reformulation shiftedEpigraph : shifted := by
  rename cap to upper
  epigraph t as objectiveBound

example : GlobalEquiv shifted shiftedEpigraph := shiftedEpigraph.equiv

/--
info: problem (u t : ℝ)
  let first := exp (u + 1)
  let second := Real.exp (u + 1)
  minimize t
  subject to
    upper : exp (u + 1) ≤ 10
    objectiveBound : first + second + exp (u + 1) ≤ t
-/
#guard_msgs in
#printp shiftedEpigraph

def directObjective :=
  problem (x : ℝ)
    minimize exp x

reformulation directEpigraph : directObjective := by
  epigraph t as objectiveBound

example : GlobalEquiv directObjective directEpigraph := directEpigraph.equiv
example (x t : ℝ) : directEpigraph.feasible (x, t) ↔ Real.exp x ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize t
  subject to
    objectiveBound : exp x ≤ t
-/
#guard_msgs in
#printp directEpigraph

def selectedOccurrence :=
  problem (x : ℝ)
    let first := exp x
    let second := Real.exp x
    minimize first + second
    subject to cap : exp x ≤ 10

reformulation selectedLift : selectedOccurrence := by
  epigraph t at first as selectedBound

example : GlobalEquiv selectedOccurrence selectedLift := selectedLift.equiv
example (x t : ℝ) : selectedLift.objective (x, t) = t + Real.exp x := rfl
example (x t : ℝ) : selectedLift.feasible (x, t) ↔
    Real.exp x ≤ 10 ∧ Real.exp x ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  let first := exp x
  let second := Real.exp x
  minimize t + second
  subject to
    cap : exp x ≤ 10
    selectedBound : first ≤ t
-/
#guard_msgs in
#printp selectedLift

def directSelectedOccurrence :=
  problem (x : ℝ)
    minimize exp x + Real.exp (x + 1)

reformulation directSelectedLift : directSelectedOccurrence := by
  epigraph t at (exp x) as selectedBound

example : GlobalEquiv directSelectedOccurrence directSelectedLift := directSelectedLift.equiv
example (x t : ℝ) : directSelectedLift.objective (x, t) = t + Real.exp (x + 1) := rfl
example (x t : ℝ) : directSelectedLift.feasible (x, t) ↔ Real.exp x ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  minimize t + Real.exp (x + 1)
  subject to
    selectedBound : exp x ≤ t
-/
#guard_msgs in
#printp directSelectedLift

macro "sourceNotationProblem" : term =>
  `(problem (x : ℝ)
      let cost := exp x
      minimize cost + exp x
      subject to cap : exp x ≤ 10)

def macroSource := sourceNotationProblem

def macroShiftCoverage : FeasibleSurjection macroSource (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

reformulation macroShifted : macroSource := by
  substitute x := u + 1 using macroShiftCoverage

example : GlobalEquiv macroSource macroShifted := macroShifted.equiv
example (u : ℝ) : macroShifted.objective u = Real.exp (u + 1) + Real.exp (u + 1) := rfl
example (u : ℝ) : macroShifted.feasible u ↔ Real.exp (u + 1) ≤ 10 := Iff.rfl

/--
info: problem (u : ℝ)
  let cost := exp (u + 1)
  minimize cost + exp (u + 1)
  subject to
    cap : exp (u + 1) ≤ 10
-/
#guard_msgs in
#printp macroShifted

-- The new decision name must remain free under the source's same-spelled lambda.
def nestedSource :=
  problem (x : ℝ)
    minimize (fun u : ℝ => exp x + u) 1

def nestedShiftCoverage : FeasibleSurjection nestedSource (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

reformulation nestedShifted : nestedSource := by
  substitute x := u + 1 using nestedShiftCoverage

example : GlobalEquiv nestedSource nestedShifted := nestedShifted.equiv
example (u : ℝ) : nestedShifted.objective u = Real.exp (u + 1) + 1 := rfl

run_cmd do
  let some presentation := Syntax.getProblemPrintPresentation? (← Lean.getEnv) ``nestedShifted
    | Lean.throwError "the nested substitution lost its print presentation"
  for view in #[presentation.compact, presentation.detailed] do
    let termSyntax ← Lean.Elab.liftMacroM view.toTermSyntax
    let termSyntax : Lean.TSyntax `term := ⟨termSyntax.raw.rewriteBottomUp fun node =>
      if node.isIdent then Lean.mkIdent node.getId.eraseMacroScopes else node⟩
    let printed ← Lean.Elab.Command.liftCoreM <| Lean.PrettyPrinter.ppTerm termSyntax
    let term ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term printed.pretty with
      | .ok term => pure term
      | .error message => Lean.throwError m!"the displayed problem does not parse: {message}\n{printed}"
    Lean.Elab.Command.liftTermElabM do
      let expected := Lean.mkConst ``nestedShifted
      let actual ← Lean.Elab.Term.elabTerm term (some (← Lean.Meta.inferType expected))
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      unless ← Lean.Meta.isDefEq (← Lean.instantiateMVars actual) expected do
        Lean.throwError "the displayed lambda captured the substituted decision variable"

-- Reuse notation other than exponential names, including a local macro.
section

local notation "growth" => Real.exp

def notationSource :=
  problem (x : ℝ)
    let cost := growth x
    minimize cost

reformulation notationTarget : notationSource := by
  epigraph t

/--
info: problem (x t : ℝ)
  let cost := growth x
  minimize t
  subject to
    epigraph_t : cost ≤ t
-/
#guard_msgs in
#printp notationTarget

end

namespace Shadowing

def exp (x : ℝ) : ℝ := x + 37

reformulation target : directObjective := by
  epigraph t

example : GlobalEquiv directObjective target := target.equiv
example (x t : ℝ) : target.feasible (x, t) ↔ Real.exp x ≤ t := Iff.rfl

-- Check the visible spelling, without the stored syntax's resolved-name hints.
run_cmd do
  let some presentation := Syntax.getProblemPrintPresentation? (← Lean.getEnv) ``target
    | Lean.throwError "the target lost its print presentation"
  for view in #[presentation.compact, presentation.detailed] do
    let termSyntax ← Lean.Elab.liftMacroM view.toTermSyntax
    let termSyntax : Lean.TSyntax `term := ⟨termSyntax.raw.rewriteBottomUp fun node =>
      if node.isIdent then Lean.mkIdent node.getId.eraseMacroScopes else node⟩
    let printed ← Lean.Elab.Command.liftCoreM <| Lean.PrettyPrinter.ppTerm termSyntax
    let term ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term printed.pretty with
      | .ok term => pure term
      | .error message => Lean.throwError m!"the displayed problem does not parse: {message}\n{printed}"
    Lean.Elab.Command.liftTermElabM do
      let expected := Lean.mkConst ``target
      let actual ← Lean.Elab.Term.elabTerm term (some (← Lean.Meta.inferType expected))
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      unless ← Lean.Meta.isDefEq (← Lean.instantiateMVars actual) expected do
        Lean.throwError "the displayed exponential was captured by the consumer namespace"

end Shadowing

namespace ChangedInstance

def sourceAdd (x y : ℝ) : ℝ := x + y

def source :=
  problem (x : ℝ)
    let cost := x + 1
    minimize cost

local instance zeroAdd : HAdd ℝ ℝ ℝ where
  hAdd _ _ := 0

reformulation target : source := by
  epigraph t

example : GlobalEquiv source target := target.equiv
example (x t : ℝ) : target.feasible (x, t) ↔ sourceAdd x 1 ≤ t := Iff.rfl

-- Exact metadata still reconstructs the selected source operation instance.
run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``target
    | Lean.throwError "the target lost its exact presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x t : ℝ) : replayed.feasible (x, t) ↔ sourceAdd x 1 ≤ t := Iff.rfl

end ChangedInstance

end
end MorewTest.Reformulation.SourceNotation
