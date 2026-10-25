/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Syntax.Presentation
import Lean.Elab.Command
import Lean.PrettyPrinter

/-!
# Source-aligned problem printing

Validate registered problem declarations and format their stored presentations
for `#printp`, preserving user names, objective sense, and constraint order.
-/

namespace Morew

open Lean Lean.Elab Lean.Elab.Command Lean.Parser

private partial def isSourceName : Name → Bool
  | .anonymous => false
  | .str parent part =>
      !part.contains '»' && (parent.isAnonymous || isSourceName parent)
  | .num _ _ => false

private def sourceNameString (description : String) (name : Name) : CoreM String := do
  let name := name.eraseMacroScopes
  unless isSourceName name do
    throwError "problem presentation metadata contains unprintable {description}"
  let tokens := Parser.getTokenTable (← getEnv)
  pure <| Name.toStringWithSep "." true name
    (isToken := fun candidate => (tokens.find? candidate).isSome)

private partial def normalizeStoredSyntax (description : String) :
    Lean.Syntax → CoreM Lean.Syntax
  | .missing =>
      throwError "problem presentation metadata contains unprintable {description} syntax"
  | .ident info _ name preresolved => do
      let name := name.eraseMacroScopes
      let rawName ← sourceNameString s!"{description} syntax" name
      pure <| .ident info rawName.toRawSubstring name preresolved
  | stx@(.node info kind args) =>
      if kind == Lean.hygieneInfoKind then
        pure stx
      else
        return .node info kind (← args.mapM (normalizeStoredSyntax description))
  | stx => pure stx

private def syntaxFormat (description : String) (stx : Lean.Syntax) : CoreM Format := do
  try
    PrettyPrinter.ppTerm ⟨← normalizeStoredSyntax description stx⟩
  catch _ =>
    throwError "problem presentation metadata contains unprintable {description} syntax"

private def nameFormat (description : String) (name : Name)
    (atomic := false) : CoreM Format := do
  let name := name.eraseMacroScopes
  if atomic && !name.isAtomic then
    throwError "problem presentation metadata contains unprintable {description} name"
  return Format.text (← sourceNameString s!"{description} name" name)

private def ensureViewNamesDistinct (what : String) (names : Array Name) : CoreM Unit := do
  for i in [:names.size] do
    for j in [0:i] do
      if names[i]!.eraseMacroScopes == names[j]!.eraseMacroScopes then
        throwError
          "problem presentation metadata contains duplicate {what} name `{names[i]!.eraseMacroScopes}`"

private def formatProblemView (view : Morew.Syntax.ProblemView) : CoreM Format := do
  if view.binders.isEmpty then
    throwError "problem presentation metadata contains no decision-variable binders"
  ensureViewNamesDistinct "decision variable" (view.binders.map (·.name))
  ensureViewNamesDistinct "constraint" (view.constraints.map (·.name))
  ensureViewNamesDistinct "model-local definition" (view.definitions.map (·.name))

  let objective ← syntaxFormat "objective" view.objective
  let mut body := match view.sense with
    | .minimize => f!"minimize {objective}"
    | .maximize => f!"maximize {objective}"
  let mut definitionFormats : Array Format := #[]
  for definition in view.definitions do
    if view.binders.any (fun binder =>
        binder.name.eraseMacroScopes == definition.name.eraseMacroScopes) then
      throwError "problem presentation metadata contains a model-local definition shadowing a decision variable"
    let name ← nameFormat "model-local definition" definition.name (atomic := true)
    let value ← syntaxFormat s!"value for model-local definition `{definition.name.eraseMacroScopes}`"
      definition.value
    let annotation ← match definition.typeSyntax? with
      | none => pure Format.nil
      | some type => do
          let type ← syntaxFormat "model-local definition type" type
          pure f!" : {type}"
    definitionFormats := definitionFormats.push f!"let {name}{annotation} := {value}"
  unless definitionFormats.isEmpty do
    body := Format.joinSep definitionFormats.toList Format.line ++ Format.line ++ body
  let mut binderGroups : Array (Array Name × String × Format) := #[]
  for binder in view.binders do
    let typeFormat ← syntaxFormat s!"type for decision variable `{binder.name.eraseMacroScopes}`"
      binder.typeSyntax
    let typeKey := typeFormat.pretty
    match binderGroups.back? with
    | some (names, previousKey, previousFormat) =>
        if previousKey == typeKey then
          binderGroups := binderGroups.set! (binderGroups.size - 1)
            (names.push binder.name, previousKey, previousFormat)
        else
          binderGroups := binderGroups.push (#[binder.name], typeKey, typeFormat)
    | none =>
        binderGroups := binderGroups.push (#[binder.name], typeKey, typeFormat)
  let binderFormats ← binderGroups.mapM fun (names, _, typeFormat) => do
    let nameFormats ← names.toList.mapM fun name =>
      nameFormat "decision variable" name (atomic := true)
    pure f!"({Format.joinSep nameFormats (Format.text " ")} : {typeFormat})"
  unless view.constraints.isEmpty do
    body := body ++ Format.line ++ "subject to"
    let mut constraintFormats : Array Format := #[]
    for constraint in view.constraints do
      let proposition ← syntaxFormat
        s!"proposition for constraint `{constraint.name.eraseMacroScopes}`"
        constraint.proposition
      let name ← nameFormat "constraint" constraint.name
      constraintFormats := constraintFormats.push f!"{name} : {proposition}"
    body := body ++ Format.nest 2
      (Format.line ++ Format.joinSep constraintFormats.toList Format.line)
  pure <| f!"problem {Format.joinSep binderFormats.toList (Format.text " ")}" ++
    Format.nest 2 (Format.line ++ body)

/-- Elaborate `#printp` by retrieving and formatting stored presentation metadata. -/
@[command_elab printProblemCmd]
def elabPrintProblem : CommandElab := fun stx => do
  let `(#printp $name:ident) := stx | throwUnsupportedSyntax
  let declName ← resolveGlobalConstNoOverload name
  let env ← getEnv
  let some view := Morew.Syntax.getProblemDisplayView? env declName
    | throwErrorAt name "declaration `{declName}` has no registered problem presentation"
  -- A `problem` term can occur as a proper subterm of another declaration.
  -- During elaboration it still sees the enclosing declaration name, so such
  -- a term may leave presentation metadata behind.  Metadata is deliberately
  -- outside the trusted semantics; validate the result type beneath the
  -- declaration's parameters before using it. Reduction also admits transparent
  -- aliases hiding further parameters or the final `Problem` type.
  let isProblem ← liftTermElabM do
    let info ← getConstInfo declName
    Lean.Meta.forallTelescopeReducing info.type
      (fun _ resultType => pure <| resultType.isAppOfArity ``Morew.Problem 2)
      (whnfType := true)
  unless isProblem do
    throwErrorAt name
      "declaration `{declName}` has problem presentation metadata but is not a `Morew.Problem`"
  logInfoAt stx (← liftCoreM <| formatProblemView view)

end Morew
