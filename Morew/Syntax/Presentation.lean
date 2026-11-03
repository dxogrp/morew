/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Core
import Morew.Syntax.Grammar
import Morew.Syntax.PowerChainView
import Lean.Elab.Term

/-!
# Source problem presentations

Source spelling, the persistent presentation registry, and syntax helpers used
by problem elaboration and reformulations.
-/

namespace Morew.Syntax

open Lean Lean.Elab Lean.Elab.Term Lean.Parser

/-- Replay a formal instance parameter by its original local name, falling
back to typeclass search in the new context. -/
syntax (name := replayInstance) "morew_replay_instance% " ident " : " term : term

@[term_elab replayInstance]
private def elabReplayInstance : TermElab := fun stx expectedType? => do
  let `(morew_replay_instance% $name:ident : $type) := stx | throwUnsupportedSyntax
  let type ← elabType type
  let result ← match ← resolveLocalName name.getId with
    | some (candidate, []) =>
        -- Restore metavariables before falling back to typeclass search.
        if ← withoutModifyingState <| Meta.isDefEq (← Meta.inferType candidate) type then
          pure candidate
        else
          Meta.synthInstance type
    | _ => Meta.synthInstance type
  ensureHasType expectedType? result

/-- Presentation data for one (nondependent) decision-variable binder. -/
structure BinderView where
  /-- The source-level name of the decision variable. -/
  name : Name
  /-- The syntax of the decision variable's declared type. -/
  typeSyntax : Lean.Syntax
  deriving Inhabited

/-- Presentation data for one named constraint. -/
structure ConstraintView where
  /-- The source-level label of the constraint. -/
  name : Name
  /-- The syntax of the proposition defining the constraint. -/
  proposition : Lean.Syntax
  deriving Inhabited

/-- A sequential, nonrecursive definition local to a problem. -/
structure DefinitionView where
  /-- The source-level name available in later definitions and all problem bodies. -/
  name : Name
  /-- Optional source-level type annotation. -/
  typeSyntax? : Option Lean.Syntax := none
  /-- Inferred type used for re-elaboration when the source omits an annotation. -/
  inferredTypeSyntax? : Option Lean.Syntax := none
  /-- Source syntax of the definition's value. -/
  value : Lean.Syntax
  deriving Inhabited

/-- The source syntax and optimization sense of a problem. -/
structure ProblemView where
  /-- Whether the problem was written as a minimization or maximization. -/
  sense : ObjectiveSense
  /-- Presentation data for the problem's decision-variable binders. -/
  binders : Array BinderView
  /-- Sequential local definitions shared by the objective and constraints. -/
  definitions : Array DefinitionView := #[]
  /-- The source syntax of the objective expression. -/
  objective : Lean.Syntax
  /-- Presentation data for the problem's named constraints. -/
  constraints : Array ConstraintView := #[]
  deriving Inhabited

/-- Display views of a reformulation. Compact output omits index proofs;
detailed output retains them for inspection at print time. -/
structure ProblemPrintPresentation where
  /-- Ordinary compact output, with finite-index bounds proofs omitted. -/
  compact : ProblemView
  /-- Ordinary output with proof details available for later inspection. -/
  detailed : ProblemView
  /-- Optional mathematical displays aligned with the compact view's constraints. -/
  mathematicalRows : Array (Option PowerChainRow) := #[]
  deriving Inhabited

-- Store reconstruction syntax and display views separately.
private structure RegisteredProblemView where
  view : ProblemView
  displayView : ProblemView
  printPresentation? : Option ProblemPrintPresentation := none
  deriving Inhabited

private initialize problemViewExtension :
    SimplePersistentEnvExtension (Name × RegisteredProblemView) (NameMap RegisteredProblemView) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries
      (fun state entry => state.insert entry.1 entry.2) {}
    addEntryFn := fun state entry => state.insert entry.1 entry.2
  }

/-- Add presentation metadata to an environment. Transformation commands can
supply a separate readable display while retaining exact syntax for replay.
Without a display override, the supplied view serves both purposes. -/
def addProblemView (env : Environment) (declName : Name)
    (view : ProblemView) (displayView? : Option ProblemView := none)
    (printPresentation? : Option ProblemPrintPresentation := none) : Environment :=
  problemViewExtension.addEntry env (declName, ⟨view, displayView?.getD view, printPresentation?⟩)

/-- Look up the syntax view registered for reconstructing a problem.
Refreshed reformulation targets retain explicit instances in this view. -/
def getProblemView? (env : Environment) (declName : Name) : Option ProblemView :=
  ((problemViewExtension.getState env).find? declName).map (·.view)

/-- Look up the readable syntax, before applying display overrides. -/
def getProblemDisplayView? (env : Environment) (declName : Name) : Option ProblemView :=
  ((problemViewExtension.getState env).find? declName).map (·.displayView)

/-- Look up optional display views for a reformulation. -/
def getProblemPrintPresentation? (env : Environment) (declName : Name) :
    Option ProblemPrintPresentation :=
  ((problemViewExtension.getState env).find? declName).bind (·.printPresentation?)

/-- Register presentation metadata in any elaborator with environment access. -/
def registerProblemView [MonadEnv m] (declName : Name)
    (view : ProblemView) (displayView? : Option ProblemView := none)
    (printPresentation? : Option ProblemPrintPresentation := none) : m Unit :=
  modifyEnv fun env => addProblemView env declName view displayView? printPresentation?

/-- Structurally replace occurrences of a source identifier in a syntax tree.
Callers must establish freshness of replacement variables and absence of
shadowing. Names are compared after erasing macro scopes. -/
partial def replaceIdent (stx : Lean.Syntax) (oldName : Name)
    (replacement : Lean.Syntax) : Lean.Syntax :=
  if stx.isIdent && stx.getId.eraseMacroScopes == oldName.eraseMacroScopes then
    replacement
  else
    match stx with
    | .node info kind args =>
        .node info kind (args.map fun child => replaceIdent child oldName replacement)
    | _ => stx

/-- Replace an identifier in local definitions, the objective, and constraints.
Decision binder types remain unchanged because they are nondependent. -/
def ProblemView.replaceIdent (view : ProblemView) (oldName : Name)
    (replacement : Lean.Syntax) : ProblemView :=
  { view with
    definitions := view.definitions.map fun definition =>
      { definition with
        typeSyntax? := definition.typeSyntax?.map
          (Syntax.replaceIdent · oldName replacement)
        inferredTypeSyntax? := definition.inferredTypeSyntax?.map
          (Syntax.replaceIdent · oldName replacement)
        value := Syntax.replaceIdent definition.value oldName replacement }
    objective := Syntax.replaceIdent view.objective oldName replacement
    constraints := view.constraints.map fun constraint =>
      { constraint with
        proposition := Syntax.replaceIdent constraint.proposition oldName replacement } }

/-- Attach the current global resolutions to identifiers without changing their
source spelling. Local variables still take precedence during elaboration,
while global references retain the namespace and `open` context in which the
problem or transformation was written. -/
partial def preResolveTerm (stx : Lean.Syntax) : TermElabM Lean.Syntax := do
  match stx with
  | .ident info rawValue value preResolved =>
      if preResolved.any fun
          | .decl _ _ => true
          | _ => false then
        pure stx
      else
        let declarations := (← resolveGlobalName value (enableLog := false)).map fun
          (name, fields) => Lean.Syntax.Preresolved.decl name fields
        pure <| .ident info rawValue value (preResolved ++ declarations)
  | .node info kind args =>
      pure <| .node info kind (← args.mapM preResolveTerm)
  | _ => pure stx

/-- Close a problem body over the model's ordered local definitions. The
decision-variable binders must already surround the resulting term. -/
def ProblemView.wrapDefinitions (view : ProblemView) (body : TSyntax `term) :
    MacroM (TSyntax `term) := do
  view.definitions.toList.foldrM (fun (definition : DefinitionView) (body : TSyntax `term) => do
    let name := Lean.mkIdent definition.name
    let value : TSyntax `term := ⟨definition.value⟩
    match definition.typeSyntax?.or definition.inferredTypeSyntax? with
    | some type =>
        let type : TSyntax `term := ⟨type⟩
        `(let $name : $type := $value; $body)
    | none => `(let $name := $value; $body)) body

/-- Reconstruct the canonical `problem` term syntax represented by a view.
Generated declaration commands can elaborate this term and then register the
same view under the newly created declaration name. -/
def ProblemView.toTermSyntax (view : ProblemView) : MacroM (TSyntax `term) := do
  if view.binders.isEmpty then
    Macro.throwError "a problem requires at least one decision variable"
  let binders ← view.binders.mapM fun (binder : BinderView) => do
    let name : TSyntax `ident := Lean.mkIdent binder.name
    let typeSyntax : TSyntax `term := ⟨binder.typeSyntax⟩
    `(problemBinder| ($name : $typeSyntax))
  let constraints ← view.constraints.mapM fun (constraint : ConstraintView) => do
    let name : TSyntax `ident := Lean.mkIdent constraint.name.eraseMacroScopes
    let proposition : TSyntax `term := ⟨constraint.proposition⟩
    `(problemConstraint| $name:ident : $proposition:term)
  let definitions : Array (TSyntax `problemDefinition) ← view.definitions.mapM fun definition => do
    let name := Lean.mkIdent definition.name
    let value : TSyntax `term := ⟨definition.value⟩
    match definition.typeSyntax?.or definition.inferredTypeSyntax? with
    | some type =>
        let type : TSyntax `term := ⟨type⟩
        `(problemDefinition| let $name : $type := $value)
    | none => `(problemDefinition| let $name := $value)
  let objective : TSyntax `term := ⟨view.objective⟩
  match view.sense, constraints.isEmpty with
  | .minimize, true => `(problem $binders:problemBinder* $definitions:problemDefinition* minimize $objective)
  | .minimize, false =>
      `(problem $binders:problemBinder* $definitions:problemDefinition* minimize $objective subject to $constraints*)
  | .maximize, true => `(problem $binders:problemBinder* $definitions:problemDefinition* maximize $objective)
  | .maximize, false =>
      `(problem $binders:problemBinder* $definitions:problemDefinition* maximize $objective subject to $constraints*)

end Morew.Syntax
