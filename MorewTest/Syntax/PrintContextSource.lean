/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Syntax
public import MorewTest.Reformulation.PrintSupport

/-!
# Source printing after its elaboration scope changes

These tests use the source printer without importing a reformulation renderer.
Visible output must still denote the original problem after names or notation change.
-/

public meta section

namespace MorewTest.Syntax.PrintContextSupport

open Lean Lean.Elab Lean.Elab.Command

private def viewParts (view : Morew.Syntax.ProblemView) : Array Lean.Syntax :=
  #[(mkIdent (if view.sense == .minimize then `minimize else `maximize)).raw, view.objective] ++
    view.binders.flatMap (fun binder => #[(mkIdent binder.name).raw, binder.typeSyntax]) ++
    view.definitions.flatMap (fun definition => #[(mkIdent definition.name).raw,
      definition.typeSyntax?.getD .missing, definition.inferredTypeSyntax?.getD .missing,
      definition.value]) ++
    view.constraints.flatMap (fun constraint => #[(mkIdent constraint.name).raw, constraint.proposition])

private def storedViews (declaration : Name) : CommandElabM (Array (Option (Array Lean.Syntax))) := do
  let environment ← getEnv
  let printed := Morew.Syntax.getProblemPrintPresentation? environment declaration
  let views := #[Morew.Syntax.getProblemView? environment declaration,
    Morew.Syntax.getProblemDisplayView? environment declaration,
    Morew.Syntax.getProblemFallbackView? environment declaration,
    Morew.Syntax.getProblemCheckedView? environment declaration,
    printed.map (·.compact), printed.map (·.detailed)].map (·.map viewParts)
  return views.push <| (Morew.Syntax.getProblemCheckedTerm? environment declaration).map (#[·])

/-- Capture actual output without removing layout needed by the problem parser. -/
def rawPrinted (declaration : Name) (proofs : Bool) : CommandElabM String := do
  let before ← storedViews declaration
  let messages ← MorewTest.Diagnostics.withSavedDiagnostics do
    let command ← if proofs then
      `(set_option pp.proofs true in #printp $(mkIdent declaration))
      else `(set_option pp.proofs false in #printp $(mkIdent declaration))
    Lean.Elab.Tactic.GuardMsgs.runAndCollectMessages command
  unless before == (← storedViews declaration) do
    throwError "printing in a changed scope modified stored presentation metadata"
  let visible := messages.toList.filter (!·.isSilent)
  let [message] := visible
    | throwError m!"expected one presentation for {declaration}, got {visible.length} diagnostics"
  unless message.severity == .information && !message.isTrace do
    throwError m!"printing {declaration} produced an unexpected diagnostic: {message.data}"
  message.data.toString

/-- Parse and check visible output in the current scope under the declaration's parameters. -/
def checkPrinted (declaration : Name) (proofs : Bool)
    (lexicalName? : Option Name := none) : CommandElabM String := do
  let printed ← rawPrinted declaration proofs
  let term ← match Parser.runParserCategory (← getEnv) `term printed with
    | .ok term => pure term
    | .error message => throwError m!"printed {declaration} does not parse: {message}\n{printed}"
  liftTermElabM do
    let info ← getConstInfo declaration
    Meta.forallTelescopeReducing info.type fun parameters _ => do
      let expected := mkAppN (mkConst declaration (info.levelParams.map Level.param)) parameters
      let actual ← Term.elabTermEnsuringType term (← Meta.inferType expected)
      Term.synthesizeSyntheticMVarsNoPostponing
      let actual ← instantiateMVars actual
      if actual.hasMVar || actual.hasLevelMVar || actual.hasSorry then
        throwError "printed output contains unresolved terms or proofs"
      unless ← Meta.isDefEq actual expected do
        throwError m!"printed {declaration} changed meaning in the current scope:\n{printed}"
      if let some name := lexicalName? then
        let binding := actual.find? fun
          | .letE actual _ _ body _ => actual.eraseMacroScopes == name && body.hasLooseBVar 0
          | _ => false
        unless binding.isSome do
          throwError m!"printing {declaration} lost lexical binding {name}"
  return printed

end MorewTest.Syntax.PrintContextSupport

end

namespace MorewTest.Syntax.PrintContextSource

open Morew
open MorewTest.Syntax.PrintContextSupport

namespace Shadowing

open Nat

def source (a : Nat) :=
  problem (x : Nat)
    minimize succ x + a

def mixed :=
  problem (x : Nat)
    minimize (let succ := fun y : Nat => y + 2; succ x) + succ x

def succ (x : Nat) : Nat := x + 37

example (a x : Nat) : (source a).objective x = Nat.succ x + a := rfl
example (x : Nat) : mixed.objective x = (x + 2) + Nat.succ x := rfl

run_cmd do
  for proofs in #[false, true] do
    discard <| checkPrinted ``source proofs
    discard <| checkPrinted ``mixed proofs (some `succ)

end Shadowing

namespace LocalNotation

section

local notation "nextValue" => Nat.succ
local notation "pairSize" => (2 : Nat)

def source (a : Nat) :=
  problem (x : Nat)
    minimize nextValue x + a

def proofSource :=
  problem (x : Nat)
    let index : Fin 2 := ⟨0, by exact (show 0 < pairSize from by decide)⟩
    minimize x + index.val

end

run_cmd do
  for declaration in #[``source, ``proofSource] do
    for proofs in #[false, true] do
      let printed ← checkPrinted declaration proofs
      if printed.contains "nextValue" || printed.contains "pairSize" then
        Lean.throwError "printing retained notation whose section has closed"

end LocalNotation

namespace ClosedNamespace

open Nat

def source (a : Nat) :=
  problem (x : Nat)
    minimize succ x + a

end ClosedNamespace

run_cmd do
  for proofs in #[false, true] do
    discard <| checkPrinted ``ClosedNamespace.source proofs

end MorewTest.Syntax.PrintContextSource
