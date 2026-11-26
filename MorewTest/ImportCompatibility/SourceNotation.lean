/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

import MorewTest.Reformulation.SourceNotation

/-! Source notation survives compiled declarations and instantiated parameters. -/

namespace MorewTest.ImportCompatibility.SourceNotation

open Morew Real
open MorewTest.Reformulation.SourceNotation
noncomputable section

reformulation concrete : (minExp 2) := by
  epigraph t as epiBound

example : GlobalEquiv (minExp 2) concrete := concrete.equiv
example (x t : ℝ) : concrete.feasible (x, t) ↔
    2 ≤ x ∧ Real.exp x ≤ t := Iff.rfl

/--
info: problem (x t : ℝ)
  let cost := exp x
  minimize t
  subject to
    lower : 2 ≤ x
    epiBound : cost ≤ t
-/
#guard_msgs in
#printp concrete

reformulation chained : (epiMinExp 3) := by
  rename lower to lowerBound
  epigraph s as secondBound

example : GlobalEquiv (epiMinExp 3) chained := chained.equiv
example (x t s : ℝ) : chained.feasible ((x, t), s) ↔
    3 ≤ x ∧ Real.exp x ≤ t ∧ t ≤ s := Iff.rfl

/--
info: problem (x t s : ℝ)
  let cost := exp x
  minimize s
  subject to
    lowerBound : 3 ≤ x
    epiBound : cost ≤ t
    secondBound : t ≤ s
-/
#guard_msgs in
#printp chained

run_cmd do
  let some view := Syntax.getProblemView? (← Lean.getEnv) ``chained
    | Lean.throwError "the imported target lost its exact presentation"
  let term ← Lean.Elab.liftMacroM view.toTermSyntax
  let name := Lean.mkIdent `replayed
  Lean.Elab.Command.elabCommand (← `(noncomputable def $name := $term))

example (x t s : ℝ) : replayed.feasible ((x, t), s) ↔
    3 ≤ x ∧ Real.exp x ≤ t ∧ t ≤ s := Iff.rfl

-- The source's local `growth` notation is unavailable in this module.
reformulation unavailableNotation : notationSource := by
  epigraph t

example : GlobalEquiv notationSource unavailableNotation := unavailableNotation.equiv
example (x t : ℝ) : unavailableNotation.feasible (x, t) ↔ Real.exp x ≤ t := Iff.rfl

run_cmd do
  let some presentation := Syntax.getProblemPrintPresentation? (← Lean.getEnv)
      ``unavailableNotation
    | Lean.throwError "the imported target lost its print presentation"
  for view in #[presentation.compact, presentation.detailed] do
    let termSyntax ← Lean.Elab.liftMacroM view.toTermSyntax
    let termSyntax : Lean.TSyntax `term := ⟨termSyntax.raw.rewriteBottomUp fun node =>
      if node.isIdent then Lean.mkIdent node.getId.eraseMacroScopes else node⟩
    let printed ← Lean.Elab.Command.liftCoreM <| Lean.PrettyPrinter.ppTerm termSyntax
    let term ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term printed.pretty with
      | .ok term => pure term
      | .error message => Lean.throwError m!"the displayed problem does not parse: {message}\n{printed}"
    Lean.Elab.Command.liftTermElabM do
      let expected := Lean.mkConst ``unavailableNotation
      let actual ← Lean.Elab.Term.elabTerm term (some (← Lean.Meta.inferType expected))
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      unless ← Lean.Meta.isDefEq (← Lean.instantiateMVars actual) expected do
        Lean.throwError "the displayed problem reused unavailable local notation"

end
end MorewTest.ImportCompatibility.SourceNotation
