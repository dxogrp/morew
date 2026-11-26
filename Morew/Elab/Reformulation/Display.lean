/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Syntax.Presentation
public meta import Lean.Elab.Term
public meta import Lean.Parser.Extension
public meta import Lean.PrettyPrinter

/-! Checked, occurrence-local syntax templates used only for readable presentations. -/

public meta section

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Term

/-- A source syntax node and the independently checked term slots inside it.
Paths identify syntax occurrences, so equal expressions can retain different spellings. -/
inductive DisplayTerm where
  /-- The checked expression, source syntax, and disjoint immediate term slots. -/
  | node (expression : Expr) (sourceSyntax : Syntax)
      (children : Array (Array Nat × DisplayTerm))
  deriving Inhabited

/-- The checked expression represented by a display template. -/
def DisplayTerm.expression : DisplayTerm → Expr
  | .node expression _ _ => expression

/-- The original syntax retained by a display template. -/
def DisplayTerm.sourceSyntax : DisplayTerm → Syntax
  | .node _ source _ => source

/-- Transport the expressions of a template without changing its syntax occurrences. -/
partial def DisplayTerm.mapExpressions (transform : Expr → Expr) : DisplayTerm → DisplayTerm
  | .node expression source children =>
      .node (transform expression) source
        (children.map fun (path, child) => (path, child.mapExpressions transform))

/-- Substitute checked bindings throughout a display template. -/
def DisplayTerm.replaceFVars (term : DisplayTerm) (oldVars newVars : Array Expr) : DisplayTerm :=
  term.mapExpressions (·.replaceFVars oldVars newVars)

/-- Close a display template over ordered bindings. -/
def DisplayTerm.abstract (term : DisplayTerm) (bindings : Array Expr) : DisplayTerm :=
  term.mapExpressions (·.abstract bindings)

/-- Open a display template with bindings in their original order. -/
def DisplayTerm.instantiate (term : DisplayTerm) (bindings : Array Expr) : DisplayTerm :=
  term.mapExpressions (·.instantiateRev bindings)

/-- Default elaboration for a candidate presentation under an expected type. -/
def defaultDisplayElaborate (source : Syntax) (type : Expr) : TermElabM Expr :=
  elabTermEnsuringType source type

private def completeDisplayExpression (expression : Expr) : Bool :=
  !expression.hasMVar && !expression.hasLevelMVar && !expression.hasSorry &&
    !expression.hasLooseBVars

-- A failed display attempt must not change diagnostics, instances, or declarations.
private def displayProbe {α : Type} (action : TermElabM α) : TermElabM (Option α) := do
  let saved ← Term.saveState
  try
    withoutErrToSorry do
      modifyThe Core.State fun state => { state with messages := {} }
      let result ← action
      if (← getThe Core.State).messages.hasErrors then return none
      return some result
  catch exception =>
    if exception.isInterrupt || exception.isMaxRecDepth || exception.isMaxHeartbeat then
      throw exception
    return none
  finally
    saved.restore (restoreInfo := true)
    setEnv saved.meta.core.env

private def checkedDisplayExpression (source : Syntax) (expected : Expr)
    (elaborate : Syntax → Expr → TermElabM Expr) : TermElabM Expr := do
  let expression ← elaborate source (← inferType expected)
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  unless completeDisplayExpression expression do
    throwError "presentation contains unresolved terms"
  unless ← isDefEq expression expected do
    throwError "presentation does not denote the checked expression"
  return expression

private structure DisplaySourceInfo where
  source : Syntax
  expression : Expr

-- Presentation elaboration may introduce hygienic aliases for existing model bindings.
private def restoreDisplayAliases (expression : Expr) (sourceContext context : LocalContext) :
    Expr :=
  expression.replace fun value => do
    let .fvar id := value | none
    if (context.find? id).isSome then none
    else do
      let declaration ← sourceContext.find? id
      let replacement ← declaration.value?
      let .fvar original := replacement | none
      guard (context.find? original).isSome
      return replacement

private partial def collectDisplaySourceInfo (tree : InfoTree)
    (originalEnv : Environment) (context : LocalContext)
    (result : Array DisplaySourceInfo) : TermElabM (Array DisplaySourceInfo) := do
  match tree with
  | .context _ child => collectDisplaySourceInfo child originalEnv context result
  | .node info children =>
      let mut result := result
      if let .ofTermInfo info := info then
        unless info.isBinder do
          let expression ← instantiateMVars info.expr
          let expression := restoreDisplayAliases expression info.lctx context
          let unavailable := expression.find? fun
            | .fvar id => (context.find? id).isNone
            | .const name _ => !originalEnv.contains name
            | _ => false
          if completeDisplayExpression expression && unavailable.isNone then
            result := result.push { source := info.stx, expression }
      for child in children do
        result ← collectDisplaySourceInfo child originalEnv context result
      return result
  | .hole _ => return result

private def uniqueDisplayExpression? (source : Syntax)
    (infos : Array DisplaySourceInfo) : Option Expr := Id.run do
  let mut found := none
  for info in infos do
    if info.source.eqWithInfo source then
      match found with
      | none => found := some info.expression
      | some previous =>
          if previous != info.expression then return none
  return found

private partial def displayTemplate (source : Syntax) (expression : Expr)
    (infos : Array DisplaySourceInfo) : DisplayTerm :=
  let rec slots (source : Syntax) (path : Array Nat) : Array (Array Nat × DisplayTerm) :=
    match uniqueDisplayExpression? source infos with
    | some expression => #[(path, displayTemplate source expression infos)]
    | none => source.getArgs.zipIdx.flatMap fun (child, index) =>
        slots child (path.push index)
  .node expression source <| source.getArgs.zipIdx.flatMap fun (child, index) =>
    slots child #[index]

/-- Recover source term slots from a successful, isolated elaboration of one checked field.
Binder-internal and ambiguous occurrences are left to ordinary delaboration. -/
def captureDisplayTerm (source : Syntax) (expected : Expr)
    (elaborate : Syntax → Expr → TermElabM Expr := defaultDisplayElaborate) :
    TermElabM (Option DisplayTerm) := do
  displayProbe do
    let originalEnv ← getEnv
    let context ← getLCtx
    let start := (← getInfoTrees).size
    withEnableInfoTree true do
      discard <| checkedDisplayExpression source expected elaborate
    let infoState ← getInfoState
    let mut infos := #[]
    for tree in infoState.trees.toArray[start:] do
      infos ← collectDisplaySourceInfo (tree.substitute infoState.assignment)
        originalEnv context infos
    return displayTemplate source expected infos

private partial def setDisplaySyntax (source : Syntax) (path : List Nat)
    (replacement : Syntax) : Syntax :=
  match path with
  | [] => replacement
  | index :: rest =>
      source.setArg index (setDisplaySyntax source[index] rest replacement)

-- Mirror the printer's visible identifier spelling before removing hidden resolutions by parsing.
private partial def visibleDisplaySyntax (source : Syntax) : CoreM Syntax := do
  match source with
  | .ident info _ name resolved =>
      let name := name.eraseMacroScopes
      let tokens := Parser.getTokenTable (← getEnv)
      let raw := Name.toStringWithSep "." true name
        (isToken := fun candidate => (tokens.find? candidate).isSome)
      return .ident info raw.toRawSubstring name resolved
  | .node info kind children =>
      if kind == Lean.hygieneInfoKind then return source
      return .node info kind (← children.mapM visibleDisplaySyntax)
  | _ => return source

private partial def cleanDisplaySyntax : Syntax → Syntax
  | .node _ kind children => .node .none kind (children.map cleanDisplaySyntax)
  | .ident _ raw name resolved => .ident .none raw name resolved
  | .atom _ value => .atom .none value
  | .missing => .missing

/-- Reuse source spelling only after checking its stored and visible meanings.
Remove source positions, comments, and whitespace from the accepted syntax. -/
def checkedDisplaySyntax (source : Syntax) (expected : Expr)
    (elaborate : Syntax → Expr → TermElabM Expr := defaultDisplayElaborate) :
    TermElabM (Option Syntax) := do
  let source := cleanDisplaySyntax source
  displayProbe do
    discard <| checkedDisplayExpression source expected elaborate
    let formatted ← PrettyPrinter.ppTerm ⟨← visibleDisplaySyntax source⟩
    let visible ← match Parser.runParserCategory (← getEnv) `term formatted.pretty with
      | .ok visible => pure visible
      | .error message => throwError "presentation is not readable syntax: {message}"
    discard <| checkedDisplayExpression visible expected elaborate
    return source

/-- Fill transported source slots and use their notation only when both the stored syntax
and its visible spelling denote the checked target. The caller controls display-policy exclusions. -/
partial def renderDisplayTerm (hint : DisplayTerm) (expected : Expr)
    (fallback : Expr → TermElabM Syntax)
    (allow : Expr → TermElabM Bool := fun _ => pure true)
    (elaborate : Syntax → Expr → TermElabM Expr := defaultDisplayElaborate) :
    TermElabM Syntax := do
  unless ← allow expected do return ← fallback expected
  let same ← displayProbe <| isDefEq hint.expression expected
  unless same == some true do return ← fallback expected
  let .node _ source children := hint
  -- Unchanged fields need one check, rather than re-elaborating every subtree.
  if let some accepted ← checkedDisplaySyntax source expected elaborate then return accepted
  let mut source := source
  for (path, child) in children do
    let replacement ← renderDisplayTerm child child.expression fallback allow elaborate
    source := setDisplaySyntax source path.toList replacement
  if let some accepted ← checkedDisplaySyntax source expected elaborate then return accepted
  fallback expected

end Morew.Elab.Reformulation
