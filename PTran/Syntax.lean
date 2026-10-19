import PTran.Core
import Lean.Elab.Command
import Lean.PrettyPrinter

/-!
# Surface syntax and presentation metadata

The semantic `Problem` structure intentionally contains only an objective and
a feasibility predicate.  This module keeps the user-facing spelling of a
problem in a persistent environment extension.  Consequently names used for
decision variables and constraints remain available to commands such as
`#printp`, without becoming part of the trusted mathematical semantics.
-/

namespace PTran
namespace Syntax

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

/-- Whether the source notation presented a minimization or maximization
problem.  Maximization is represented semantically by `OrderDual`. -/
inductive ObjectiveSense where
  | minimize
  | maximize
  deriving Inhabited, BEq, Repr

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

/-- The source-level view of a problem.  None of these fields affects the
meaning of the corresponding `Problem`. -/
structure ProblemView where
  /-- Whether the problem was written as a minimization or maximization. -/
  sense : ObjectiveSense
  /-- Presentation data for the problem's decision-variable binders. -/
  binders : Array BinderView
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

end Syntax

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser
open Syntax

/-- Syntax category for an explicitly typed, nondependent problem binder. -/
declare_syntax_cat problemBinder
/-- Parse one or more decision-variable names sharing an explicit type. -/
syntax (name := problemBinderStx) "(" ident+ " : " term ")" : problemBinder

/-- Syntax category for a labeled problem constraint. -/
declare_syntax_cat problemConstraint
/-- Parse a constraint label followed by its proposition. -/
syntax (name := problemConstraintStx) ident " : " term : problemConstraint

/-- An unconstrained minimization problem with one or more explicitly typed,
nondependent decision-variable binders. -/
syntax (name := minimizeProblemTerm)
  "problem " problemBinder+ ppLine "minimize " term : term
/-- A constrained minimization problem with explicitly typed, nondependent
decision-variable binders and an indented block of named constraints. -/
syntax (name := minimizeConstrainedProblemTerm)
  "problem " problemBinder+ ppLine "minimize " term ppLine
  "subject " "to" ppLine
    ppIndent(many1Indent(problemConstraint)) : term
/-- An unconstrained maximization problem with one or more explicitly typed,
nondependent decision-variable binders. -/
syntax (name := maximizeProblemTerm)
  "problem " problemBinder+ ppLine "maximize " term : term
/-- A constrained maximization problem with explicitly typed, nondependent
decision-variable binders and an indented block of named constraints. -/
syntax (name := maximizeConstrainedProblemTerm)
  "problem " problemBinder+ ppLine "maximize " term ppLine
  "subject " "to" ppLine
    ppIndent(many1Indent(problemConstraint)) : term

namespace Syntax

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
  let objective : TSyntax `term := ⟨view.objective⟩
  match view.sense, constraints.isEmpty with
  | .minimize, true => `(problem $binders* minimize $objective)
  | .minimize, false =>
      `(problem $binders* minimize $objective subject to $constraints*)
  | .maximize, true => `(problem $binders* maximize $objective)
  | .maximize, false =>
      `(problem $binders* maximize $objective subject to $constraints*)

end Syntax

private def decodeBinder (stx : Lean.Syntax) : MacroM (Array PTran.Syntax.BinderView) := do
  match stx with
  | `(problemBinder| ($names:ident* : $typeSyntax:term)) =>
      pure <| names.map fun name => { name := name.getId, typeSyntax := typeSyntax }
  | _ => Macro.throwErrorAt stx "invalid problem binder"

private def decodeConstraint (stx : Lean.Syntax) : MacroM PTran.Syntax.ConstraintView := do
  match stx with
  | `(problemConstraint| $name:ident : $proposition:term) =>
      pure { name := name.getId, proposition := proposition }
  | _ => Macro.throwErrorAt stx "invalid named constraint"

private def mkProductType : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => Macro.throwError "a problem requires at least one decision variable"
  | first :: rest => rest.foldlM (fun accumulated typeSyntax => do
      `($accumulated × $typeSyntax)) first

private def mkProductPattern : List (TSyntax `ident) → MacroM (TSyntax `term)
  | [] => Macro.throwError "a problem requires at least one decision variable"
  | first :: rest =>
      let restTerms : List (TSyntax `term) := rest.map fun name => ⟨name.raw⟩
      restTerms.foldlM (fun accumulated name => do
        `(⟨$accumulated, $name⟩)) ⟨first.raw⟩

private partial def mkConstraintConjunction : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `(True)
  | [proposition] => pure proposition
  | proposition :: rest => do
      let tail ← mkConstraintConjunction rest
      `($proposition ∧ $tail)

private def ensureDistinct (what : String) (names : Array Name) (refs : Array Lean.Syntax) :
    MacroM Unit := do
  for i in [:names.size] do
    for j in [0:i] do
      if names[i]!.eraseMacroScopes == names[j]!.eraseMacroScopes then
        Macro.throwErrorAt refs[i]!
          s!"duplicate {what} name `{names[i]!.eraseMacroScopes}`"

private def elaborateProblem (_stx : Lean.Syntax) (bindersStx : Array Lean.Syntax)
    (sense : PTran.Syntax.ObjectiveSense) (objective : TSyntax `term)
    (constraintsStx : Array Lean.Syntax) (expectedType? : Option Expr) : TermElabM Expr := do
  let binderGroups ← liftMacroM <| bindersStx.mapM decodeBinder
  let binders := binderGroups.foldl (init := #[]) (fun result group => result ++ group)
  let constraints ← liftMacroM <| constraintsStx.mapM decodeConstraint
  let binderRefs := bindersStx.flatMap fun ref =>
    match ref with
    | `(problemBinder| ($names:ident* : $_)) => names.map fun _ => ref
    | _ => #[]
  liftMacroM <| ensureDistinct "decision variable" (binders.map (fun binder => binder.name)) binderRefs
  liftMacroM <| ensureDistinct "constraint" (constraints.map (fun constraint => constraint.name)) constraintsStx

  let binderNames : List (TSyntax `ident) := bindersStx.toList.flatMap fun binder =>
    match binder with
    | `(problemBinder| ($names:ident* : $_)) => names.toList
    | _ => []
  let binderTypes : List (TSyntax `term) := binders.toList.map fun
    (binder : PTran.Syntax.BinderView) => ⟨binder.typeSyntax⟩
  let constraintTerms : List (TSyntax `term) :=
    constraints.toList.map fun (constraint : PTran.Syntax.ConstraintView) => ⟨constraint.proposition⟩
  let productType ← liftMacroM <| mkProductType binderTypes
  let productPattern ← liftMacroM <| mkProductPattern binderNames
  let feasible ← liftMacroM <| mkConstraintConjunction constraintTerms
  let resultSyntax ← match sense with
    | .minimize =>
        `(PTran.Problem.mk
          (fun ($productPattern : $productType) => $objective)
          (fun ($productPattern : $productType) => $feasible))
    | .maximize =>
        `(PTran.Problem.mk (V := OrderDual _)
          (fun ($productPattern : $productType) => $objective)
          (fun ($productPattern : $productType) => $feasible))
  let result ← elabTerm resultSyntax expectedType?
  if let some declName ← getDeclName? then
    let binders ← binders.mapM fun binder => do
      pure { binder with typeSyntax := ← PTran.Syntax.preResolveTerm binder.typeSyntax }
    let objective ← PTran.Syntax.preResolveTerm objective.raw
    let constraints ← constraints.mapM fun constraint => do
      pure {
        constraint with
        proposition := ← PTran.Syntax.preResolveTerm constraint.proposition
      }
    PTran.Syntax.registerProblemView declName {
      sense
      binders
      objective
      constraints
    }
  pure result

/-- Elaborate an unconstrained minimization problem term. -/
@[term_elab minimizeProblemTerm]
def elabProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* minimize $objective:term) =>
      elaborateProblem stx binders .minimize objective #[] expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate a constrained minimization problem term. -/
@[term_elab minimizeConstrainedProblemTerm]
def elabConstrainedMinProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* minimize $objective:term
      subject to $constraints:problemConstraint*) =>
      elaborateProblem stx binders .minimize objective constraints expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate an unconstrained maximization problem term. -/
@[term_elab maximizeProblemTerm]
def elabMaxProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* maximize $objective:term) =>
      elaborateProblem stx binders .maximize objective #[] expectedType?
  | _ => throwUnsupportedSyntax

/-- Elaborate a constrained maximization problem term. -/
@[term_elab maximizeConstrainedProblemTerm]
def elabConstrainedMaxProblem : TermElab := fun stx expectedType? => do
  match stx with
  | `(problem $binders:problemBinder* maximize $objective:term
      subject to $constraints:problemConstraint*) =>
      elaborateProblem stx binders .maximize objective constraints expectedType?
  | _ => throwUnsupportedSyntax

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

private def formatProblemView (view : PTran.Syntax.ProblemView) : CoreM Format := do
  if view.binders.isEmpty then
    throwError "problem presentation metadata contains no decision-variable binders"
  ensureViewNamesDistinct "decision variable" (view.binders.map (·.name))
  ensureViewNamesDistinct "constraint" (view.constraints.map (·.name))

  let objective ← syntaxFormat "objective" view.objective
  let mut body := match view.sense with
    | .minimize => f!"minimize {objective}"
    | .maximize => f!"maximize {objective}"
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

/-- Print the source-aligned mathematical presentation of a registered problem. -/
syntax (name := printProblemCmd) "#printp " ident : command

/-- Elaborate `#printp` by retrieving and formatting stored presentation metadata. -/
@[command_elab printProblemCmd]
def elabPrintProblem : CommandElab := fun stx => do
  let `(#printp $name:ident) := stx | throwUnsupportedSyntax
  let declName ← resolveGlobalConstNoOverload name
  let env ← getEnv
  let some view := PTran.Syntax.getProblemView? env declName
    | throwErrorAt name "declaration `{declName}` has no registered problem presentation"
  -- A `problem` term can occur as a proper subterm of another declaration.
  -- During elaboration it still sees the enclosing declaration name, so such
  -- a term may leave presentation metadata behind.  Metadata is deliberately
  -- outside the trusted semantics; validate the declaration's actual type
  -- before using it.  WHNF also admits transparent aliases of `Problem`.
  let declType ← liftTermElabM do
    let info ← getConstInfo declName
    Lean.Meta.whnf info.type
  unless declType.isAppOfArity ``PTran.Problem 2 do
    throwErrorAt name
      "declaration `{declName}` has problem presentation metadata but is not a `PTran.Problem`"
  logInfoAt stx (← liftCoreM <| formatProblemView view)

end PTran
