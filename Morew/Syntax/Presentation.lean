import Morew.Core
import Morew.Syntax.Grammar
import Lean.Elab.Term

/-!
# Source problem presentations

Source spelling, the persistent presentation registry, and syntax helpers used
by problem elaboration and reformulations. This metadata stays outside the
semantic `Problem` and its checked certificates.
-/

namespace Morew.Syntax

open Lean Lean.Elab Lean.Elab.Term Lean.Parser

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

/-- One sequential, nonrecursive model-local definition. Its name denotes a
binding, even when another definition has the same value. -/
structure DefinitionView where
  /-- The source-level name available in later definitions and all problem bodies. -/
  name : Name
  /-- Optional source-level type annotation. -/
  typeSyntax? : Option Lean.Syntax := none
  /-- Checked inferred type retained for re-elaboration when the source omitted
  an annotation. This is not printed as an explicit source annotation. -/
  inferredTypeSyntax? : Option Lean.Syntax := none
  /-- Source syntax of the definition's value. -/
  value : Lean.Syntax
  deriving Inhabited

/-- The source-level view of a problem.  None of these fields affects the
meaning of the corresponding `Problem`. -/
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

private initialize problemViewExtension :
    SimplePersistentEnvExtension (Name × ProblemView) (NameMap ProblemView) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := mkStateFromImportedEntries
      (fun state entry => state.insert entry.1 entry.2) {}
    addEntryFn := fun state entry => state.insert entry.1 entry.2
  }

/-- Add presentation metadata to an environment.  Transformation commands use
this function when they generate a new problem declaration. -/
def addProblemView (env : Environment) (declName : Name)
    (view : ProblemView) : Environment :=
  problemViewExtension.addEntry env (declName, view)

/-- Look up the presentation metadata registered for a problem declaration. -/
def getProblemView? (env : Environment) (declName : Name) : Option ProblemView :=
  (problemViewExtension.getState env).find? declName

/-- Register presentation metadata in any elaborator with environment access. -/
def registerProblemView [MonadEnv m] (declName : Name)
    (view : ProblemView) : m Unit :=
  modifyEnv fun env => addProblemView env declName view

/-- Structurally replace occurrences of a source identifier in a syntax tree.
This low-level helper does not interpret nested binders; transformation
commands must first check that the replacement variables are fresh and that
the selected problem variable is not shadowed in the expression.  Comparing
names without macro scopes makes it work for both parsed and
command-generated problem views. -/
partial def replaceIdent (stx : Lean.Syntax) (oldName : Name)
    (replacement : Lean.Syntax) : Lean.Syntax :=
  if stx.isIdent && stx.getId.eraseMacroScopes == oldName.eraseMacroScopes then
    replacement
  else
    match stx with
    | .node info kind args =>
        .node info kind (args.map fun child => replaceIdent child oldName replacement)
    | _ => stx

/-- Apply identifier replacement to the objective and all constraints of a
problem view.  Binder types are unchanged because v1 binders are
nondependent. -/
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
source spelling.  Local variables still take precedence during elaboration,
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
