/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Reformulation.Conic
import MorewTest.Reformulation.PrintSupport

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

-- Lexical lets must not be mistaken for aliases of the problem's decision bindings.
def innerLet :=
  problem (x : ℝ)
    minimize let y := x; exp y + y

def innerLetCoverage : FeasibleSurjection innerLet (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

reformulation innerLetShifted : innerLet := by
  substitute x := u + 1 using innerLetCoverage

example : GlobalEquiv innerLet innerLetShifted := innerLetShifted.equiv
example (u : ℝ) : innerLetShifted.objective u = Real.exp (u + 1) + (u + 1) := rfl

def nestedLets :=
  problem (x : ℝ)
    minimize let y := x; let z := y; exp z + y

def nestedLetsCoverage : FeasibleSurjection nestedLets (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

reformulation nestedLetsShifted : nestedLets := by
  substitute x := u + 1 using nestedLetsCoverage

example : GlobalEquiv nestedLets nestedLetsShifted := nestedLetsShifted.equiv
example (u : ℝ) : nestedLetsShifted.objective u = Real.exp (u + 1) + (u + 1) := rfl

-- Reusing one syntax object for distinct bindings must not merge their identities.
macro "aliasProblem" : term => do
  let x := Lean.mkIdent `x
  `(problem ($x : ℝ) minimize let $x := $x; exp $x + $x)

def macroLet := aliasProblem

def macroLetCoverage : FeasibleSurjection macroLet (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

reformulation macroLetShifted : macroLet := by
  substitute x := u + 1 using macroLetCoverage

example : GlobalEquiv macroLet macroLetShifted := macroLetShifted.equiv
example (u : ℝ) : macroLetShifted.objective u = Real.exp (u + 1) + (u + 1) := rfl

run_cmd do
  for (target, names) in #[(``innerLetShifted, #[`y]), (``nestedLetsShifted, #[`y, `z]),
      (``macroLetShifted, #[`x])] do
    let some presentation := Syntax.getProblemPrintPresentation? (← Lean.getEnv) target
      | Lean.throwError "the substitution lost its print presentation"
    for view in #[presentation.compact, presentation.detailed] do
      Lean.Elab.Command.liftTermElabM do
        Lean.Meta.withLocalDeclD view.binders[0]!.name (Lean.mkConst ``Real) fun _ => do
          let objective ← Lean.Elab.Term.elabTerm view.objective (some (Lean.mkConst ``Real))
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          let mut body ← Lean.instantiateMVars objective
          for name in names do
            let .letE actual _ _ rest _ := body.consumeMData
              | Lean.throwError "the displayed objective lost a lexical binding"
            unless actual.eraseMacroScopes == name && rest.hasLooseBVar 0 do
              Lean.throwError "the displayed objective lost the name or use of a lexical binding"
            body := rest
      let termSyntax ← Lean.Elab.liftMacroM view.toTermSyntax
      let termSyntax : Lean.TSyntax `term := ⟨termSyntax.raw.rewriteBottomUp fun node =>
        if node.isIdent then Lean.mkIdent node.getId.eraseMacroScopes else node⟩
      let printed ← Lean.Elab.Command.liftCoreM <| Lean.PrettyPrinter.ppTerm termSyntax
      let term ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term printed.pretty with
        | .ok term => pure term
        | .error message => Lean.throwError m!"the displayed problem does not parse: {message}\n{printed}"
      Lean.Elab.Command.liftTermElabM do
        let expected := Lean.mkConst target
        let actual ← Lean.Elab.Term.elabTerm term (some (← Lean.Meta.inferType expected))
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        unless ← Lean.Meta.isDefEq (← Lean.instantiateMVars actual) expected do
          Lean.throwError "the displayed lexical bindings changed the substituted objective"
    let some exact := Syntax.getProblemView? (← Lean.getEnv) target
      | Lean.throwError "the substitution lost its exact presentation"
    let term ← Lean.Elab.liftMacroM exact.toTermSyntax
    Lean.Elab.Command.liftTermElabM do
      let expected := Lean.mkConst target
      let actual ← Lean.Elab.Term.elabTerm term (some (← Lean.Meta.inferType expected))
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      unless ← Lean.Meta.isDefEq (← Lean.instantiateMVars actual) expected do
        Lean.throwError "the exact presentation changed the substituted objective"

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

namespace MixedFields

open Morew.Conic

-- A cast in one subexpression must not discard notation in its siblings.
def castSource (n : ℕ) :=
  problem (x : ℝ)
    let cost := exp x + (n : ℝ)
    minimize cost + exp x
    subject to cap : exp x + (n : ℝ) ≤ 100

def castCoverage (n : ℕ) : FeasibleSurjection (castSource n) (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

def nestedCastSource (n : ℕ) :=
  problem (x : ℝ)
    minimize let y := x; exp y + (n : ℝ) + y

def nestedCastCoverage (n : ℕ) :
    FeasibleSurjection (nestedCastSource n) (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

def lambdaCastSource (n : ℕ) :=
  problem (x : ℝ)
    minimize (fun u : ℝ => exp x + (n : ℝ) + u) 1

def lambdaCastCoverage (n : ℕ) :
    FeasibleSurjection (lambdaCastSource n) (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

section

variable (n : ℕ)

reformulation castEpigraph : (castSource n) := by
  epigraph t

reformulation castShifted : (castSource n) := by
  substitute x := u + 1 using castCoverage n

reformulation nestedCastShifted : (nestedCastSource n) := by
  substitute x := u + 1 using nestedCastCoverage n

reformulation lambdaCastShifted : (lambdaCastSource n) := by
  substitute x := u + 1 using lambdaCastCoverage n

example : GlobalEquiv (castSource n) (castEpigraph n) := castEpigraph.equiv n
example : GlobalEquiv (castSource n) (castShifted n) := castShifted.equiv n
example : GlobalEquiv (nestedCastSource n) (nestedCastShifted n) := nestedCastShifted.equiv n
example : GlobalEquiv (lambdaCastSource n) (lambdaCastShifted n) := lambdaCastShifted.equiv n
example (x t : ℝ) : (castEpigraph n).feasible (x, t) ↔
    Real.exp x + (n : ℝ) ≤ 100 ∧ Real.exp x + (n : ℝ) + Real.exp x ≤ t := Iff.rfl
example (u : ℝ) : (castShifted n).objective u =
    Real.exp (u + 1) + (n : ℝ) + Real.exp (u + 1) := rfl
example (u : ℝ) : (nestedCastShifted n).objective u =
    Real.exp (u + 1) + (n : ℝ) + (u + 1) := rfl
example (u : ℝ) : (lambdaCastShifted n).objective u =
    Real.exp (u + 1) + (n : ℝ) + 1 := rfl

end

run_cmd do
  for (declaration, argument) in #[(``castEpigraph, "x"), (``castShifted, "(u + 1)")] do
    for proofs in #[false, true] do
      let printed ← MorewTest.Reformulation.PrintDetails.printed declaration proofs
      for fragment in #[s!"let cost := exp {argument}", s!"cap : exp {argument}"] do
        unless printed.contains fragment do
          Lean.throwError m!"a cast discarded neighboring source notation: {printed}"
      if printed.contains "rexp" then
        Lean.throwError m!"a cast changed an unrelated exponential spelling: {printed}"

theorem sourceIndexBound : 0 < 2 := by decide

def proofSource :=
  problem (x t : ℝ) (v : Fin 2 → ℝ)
    let cost := exp x + v ⟨0, sourceIndexBound⟩
    minimize cost
    subject to curve : exp x ≤ t

reformulation proofCone : proofSource := by
  conic at curve

example : GlobalEquiv proofSource proofCone := proofCone.equiv
example (x t : ℝ) (v : Fin 2 → ℝ) :
    proofCone.objective ((x, t), v) = Real.exp x + v ⟨0, sourceIndexBound⟩ := rfl
example (x t : ℝ) (v : Fin 2 → ℝ) :
    proofCone.feasible ((x, t), v) ↔ (x, 1, t) ∈ EXP := Iff.rfl

run_cmd do
  MorewTest.Reformulation.PrintDetails.checkDetails ``proofCone "sourceIndexBound"
    #["let cost := exp x", "curve_conic_1 : (x, 1, t) ∈ EXP"]

-- Partial rendering must not capture the new decision variable beneath a source lambda.
def lambdaProofSource (v : Fin 2 → ℝ) :=
  problem (x : ℝ)
    minimize (fun u : ℝ => exp x + v ⟨0, sourceIndexBound⟩ + u) 1

def lambdaProofCoverage (v : Fin 2 → ℝ) :
    FeasibleSurjection (lambdaProofSource v) (fun u : ℝ => u + 1) where
  preimage point := point.1 - 1
  rightInverse _ := sub_add_cancel _ _

section

variable (v : Fin 2 → ℝ)

reformulation lambdaProofShifted : (lambdaProofSource v) := by
  substitute x := u + 1 using lambdaProofCoverage v

example : GlobalEquiv (lambdaProofSource v) (lambdaProofShifted v) := lambdaProofShifted.equiv v
example (u : ℝ) : (lambdaProofShifted v).objective u =
    Real.exp (u + 1) + v ⟨0, sourceIndexBound⟩ + 1 := rfl

end

-- A visible term slot does not justify preserving unsupported operations hidden by a macro.
macro "hiddenCast%(" value:term "," count:term ")" : term =>
  `($value + ($count : ℝ))

macro "hiddenIndex%(" value:term "," vector:term ")" : term =>
  `($value + $vector ⟨0, sourceIndexBound⟩)

def hiddenSource (n : ℕ) :=
  problem (x : ℝ) (v : Fin 2 → ℝ)
    let shifted := hiddenCast%(exp x, n)
    let cost := hiddenIndex%(exp x, v)
    minimize shifted + cost

section

variable (n : ℕ)

reformulation hiddenEpigraph : (hiddenSource n) := by
  epigraph t

example : GlobalEquiv (hiddenSource n) (hiddenEpigraph n) := hiddenEpigraph.equiv n
example (x t : ℝ) (v : Fin 2 → ℝ) : (hiddenEpigraph n).feasible ((x, v), t) ↔
    Real.exp x + (n : ℝ) + (Real.exp x + v ⟨0, sourceIndexBound⟩) ≤ t := Iff.rfl

end

run_cmd do
  MorewTest.Reformulation.PrintDetails.checkDetails ``hiddenEpigraph "sourceIndexBound"
    #["let shifted", "let cost"]
  for proofs in #[false, true] do
    let printed ← MorewTest.Reformulation.PrintDetails.printed ``hiddenEpigraph proofs
    if printed.contains "hiddenCast%" || printed.contains "hiddenIndex%" then
      Lean.throwError m!"a macro hid unsupported casts or proof details from rendering: {printed}"

-- Replay the exact metadata and the visible displays under their formal parameters.
-- Compact finite-index proofs are intentionally omitted, so only their detailed view replays.
run_cmd do
  for (declaration, compactReplay) in #[(``castEpigraph, true), (``castShifted, true),
      (``nestedCastShifted, true), (``lambdaCastShifted, true), (``proofCone, false),
      (``lambdaProofShifted, false), (``hiddenEpigraph, false)] do
    let some exact := Syntax.getProblemView? (← Lean.getEnv) declaration
      | Lean.throwError "mixed-field rendering lost exact replay metadata"
    let some presentation := Syntax.getProblemPrintPresentation? (← Lean.getEnv) declaration
      | Lean.throwError "mixed-field rendering lost its print presentation"
    let exactTerm ← Lean.Elab.liftMacroM exact.toTermSyntax
    Lean.Elab.Command.liftTermElabM do
      let info ← Lean.getConstInfo declaration
      Lean.Meta.forallTelescopeReducing info.type fun parameters _ => do
        let expected := Lean.mkAppN (Lean.mkConst declaration) parameters
        let actual ← Lean.Elab.Term.elabTerm exactTerm (some (← Lean.Meta.inferType expected))
        Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
        unless ← Lean.Meta.isDefEq (← Lean.instantiateMVars actual) expected do
          Lean.throwError "mixed-field rendering changed exact replay"
    let views := if compactReplay then #[(presentation.compact, false), (presentation.detailed, true)]
      else #[(presentation.detailed, true)]
    for (view, proofs) in views do
      let messages ← MorewTest.Diagnostics.withSavedDiagnostics do
        let command ← if proofs then
          `(set_option pp.proofs true in #printp $(Lean.mkIdent declaration))
          else `(set_option pp.proofs false in #printp $(Lean.mkIdent declaration))
        Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages command
      let visible := messages.toList.filter (!·.isSilent)
      let [message] := visible
        | Lean.throwError "expected one mixed-field print presentation"
      unless message.severity == .information && !message.isTrace do
        Lean.throwError m!"mixed-field printing produced an unexpected diagnostic: {message.data}"
      let printed ← message.data.toString
      let term ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term printed with
        | .ok term => pure term
        | .error message =>
            Lean.throwError m!"the mixed-field display for {declaration} does not parse: {message}\n{printed}"
      Lean.Elab.Command.liftTermElabM do
        let info ← Lean.getConstInfo declaration
        Lean.Meta.forallTelescopeReducing info.type fun parameters _ => do
          let expected := Lean.mkAppN (Lean.mkConst declaration) parameters
          let actual ← Lean.Elab.Term.elabTerm term (some (← Lean.Meta.inferType expected))
          Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
          unless ← Lean.Meta.isDefEq (← Lean.instantiateMVars actual) expected do
            Lean.throwError "mixed-field rendering changed the displayed problem"
          if declaration == ``nestedCastShifted then
            Lean.Meta.withLocalDeclD view.binders[0]!.name (Lean.mkConst ``Real) fun _ => do
              let objective ← Lean.Elab.Term.elabTerm view.objective (some (Lean.mkConst ``Real))
              Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
              let .letE name _ _ body _ := (← Lean.instantiateMVars objective).consumeMData
                | Lean.throwError "mixed-field fallback lost its lexical binding"
              unless name.eraseMacroScopes == `y && body.hasLooseBVar 0 do
                Lean.throwError "mixed-field fallback lost the lexical binding's name or use"

-- Equal target predicates still require separate source occurrences to cover their rendering.
def repeatedMembershipSource :=
  problem (x : ℝ)
    minimize x
    subject to group : x ∈ Cone.nonnegScalar.carrier ∧ 0 ≤ x

reformulation repeatedMembershipTarget : repeatedMembershipSource := by
  conic

example : GlobalEquiv repeatedMembershipSource repeatedMembershipTarget :=
  repeatedMembershipTarget.equiv
example : repeatedMembershipTarget.conicForm.data.rowCount = 2 := rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.withLocalDeclD `x (Lean.mkConst ``Real) fun x => do
    let name := Lean.mkIdent `x
    let source ← `($name ∈ Cone.nonnegScalar.carrier ∧ 0 ≤ $name)
    let expectedSyntax ←
      `($name ∈ Cone.nonnegScalar.carrier ∧ $name ∈ Cone.nonnegScalar.carrier)
    let expected ← Lean.Elab.Term.elabTermEnsuringType expectedSyntax (Lean.mkSort .zero)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expected ← Lean.instantiateMVars expected
    let displayed ← Morew.Elab.Reformulation.sourceDisplayTerm source expected #[(x.fvarId!, `x)]
    let actual ← Lean.Elab.Term.elabTermEnsuringType displayed (Lean.mkSort .zero)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let actual ← Lean.instantiateMVars actual
    unless (← Lean.Meta.isDefEq actual expected) && actual.isAppOfArity ``And 2 &&
        actual.getAppArgs.all (·.isAppOfArity ``Membership.mem 5) do
      Lean.throwError "one source slot hid a distinct generated membership occurrence"

end MixedFields

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

namespace ConditionalSources

-- Concrete arguments can expose a problem whose formal body is still a conditional.
def source (flag : Bool) :=
  if flag then
    problem (x : ℝ) minimize exp x subject to lower : 0 ≤ x
  else
    problem (x : ℝ) minimize x ^ 2 subject to lower : 0 ≤ x

reformulation exponential : (source true) := by
  epigraph t

reformulation quadratic : (source false) := by
  epigraph t

example : GlobalEquiv (source true) exponential := exponential.equiv
example : GlobalEquiv (source false) quadratic := quadratic.equiv
example (x t : ℝ) : exponential.feasible (x, t) ↔
    0 ≤ x ∧ Real.exp x ≤ t := Iff.rfl
example (x t : ℝ) : quadratic.feasible (x, t) ↔
    0 ≤ x ∧ x ^ 2 ≤ t := Iff.rfl

run_cmd do
  for (declaration, bound) in #[(``exponential, "rexp x ≤ t"), (``quadratic, "x ^ 2 ≤ t")] do
    for proofs in #[false, true] do
      let printed ← MorewTest.Reformulation.PrintDetails.printed declaration proofs
      unless printed == "problem (x t : ℝ) minimize t subject to lower : 0 ≤ x epigraph_t : " ++
          bound do
        Lean.throwError m!"specialized source fallback changed the displayed problem: {printed}"

end ConditionalSources

end
end MorewTest.Reformulation.SourceNotation
