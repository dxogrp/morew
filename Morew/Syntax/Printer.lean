/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

module

public import Morew.Syntax.Presentation
public meta import Lean.Elab.Command
public meta import Lean.PrettyPrinter

/-!
# Problem printing

Validate registered problem declarations and format their stored presentations
for `#printp`, preserving user names, objective sense, and constraint order.

Reformulations carry compact and detailed display views.
Recognized power-cone representations use a marked mathematical display by default;
`pp.proofs true` selects ordinary Lean syntax with proof details at print time.
-/

public meta section

namespace Morew

open Lean Lean.Elab Lean.Elab.Command Lean.Parser

/-- Refresh a cached problem display using a representation-aware renderer. -/
structure ProblemPrintRefresher where
  /-- Render the checked declaration in the current printing scope. -/
  refresh : Name → Morew.Syntax.ProblemView → CommandElabM Morew.Syntax.ProblemPrintPresentation

private unsafe def mkProblemPrintAttributeUnsafe (ref : Name) :
    IO (KeyedDeclsAttribute ProblemPrintRefresher) :=
  KeyedDeclsAttribute.init {
    name := `morew_problem_print_refresher
    descr := "internal current-scope problem presentation renderer"
    valueTypeName := ``ProblemPrintRefresher
  } ref

@[implemented_by mkProblemPrintAttributeUnsafe]
private opaque mkProblemPrintAttribute (ref : Name) :
  IO (KeyedDeclsAttribute ProblemPrintRefresher)

/-- Optional renderer supplied by reformulation support, without a printer import cycle. -/
initialize problemPrintAttribute : KeyedDeclsAttribute ProblemPrintRefresher ←
  mkProblemPrintAttribute decl_name%

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

private def formatProblemView (view : Morew.Syntax.ProblemView)
    (mathematicalRows : Array (Option Morew.Syntax.PowerChainRow) := #[]) : CoreM Format := do
  if view.binders.isEmpty then
    throwError "problem presentation metadata contains no optimization-variable binders"
  unless mathematicalRows.isEmpty || mathematicalRows.size == view.constraints.size do
    throwError "problem presentation metadata contains misaligned mathematical rows"
  ensureViewNamesDistinct "optimization variable" (view.binders.map (·.name))
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
      throwError "problem presentation metadata contains a model-local definition shadowing an optimization variable"
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
    let typeFormat ← syntaxFormat s!"type for optimization variable `{binder.name.eraseMacroScopes}`"
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
      nameFormat "optimization variable" name (atomic := true)
    pure f!"({Format.joinSep nameFormats (Format.text " ")} : {typeFormat})"
  unless view.constraints.isEmpty do
    body := body ++ Format.line ++ "subject to"
    let mut constraintFormats : Array Format := #[]
    for constraint in view.constraints, index in [:view.constraints.size] do
      let description := s!"proposition for constraint `{constraint.name.eraseMacroScopes}`"
      let proposition ← match mathematicalRows[index]?.getD none with
        | some row => row.format (syntaxFormat description)
        | none => syntaxFormat description constraint.proposition
      let name ← nameFormat "constraint" constraint.name
      constraintFormats := constraintFormats.push f!"{name} : {proposition}"
    body := body ++ Format.nest 2
      (Format.line ++ Format.joinSep constraintFormats.toList Format.line)
  let marker := if mathematicalRows.any Option.isSome then
      Format.text "-- Mathematical view" ++ Format.line else Format.nil
  pure <| marker ++ f!"problem {Format.joinSep binderFormats.toList (Format.text " ")}" ++
    Format.nest 2 (Format.line ++ body)

private partial def parameterNames : Expr → Array Name
  | .lam name _ body _ => #[name.eraseMacroScopes] ++ parameterNames body
  | .mdata _ body => parameterNames body
  | _ => #[]

private def withPrintParameters (declName : Name) (view : Morew.Syntax.ProblemView)
    (action : Expr → TermElabM α) : TermElabM α := do
  let info ← getConstInfo declName
  let target := mkConst declName (info.levelParams.map Level.param)
  Meta.withLCtx {} {} do
    Meta.forallTelescopeReducing info.type fun parameters _ => do
      let bodyNames := info.value?.map parameterNames |>.getD #[]
      let names ← parameters.mapIdxM fun index parameter =>
        return bodyNames[index]?.getD (← parameter.fvarId!.getDecl).userName.eraseMacroScopes
      let modelNames := (view.binders.map (·.name) ++ view.definitions.map (·.name)).foldl
        (fun names name => names.insert name.eraseMacroScopes) ({} : NameSet)
      let reserved := names.foldl (fun names name => names.insert name) modelNames
      let mut occupied := modelNames
      let mut context ← getLCtx
      for parameter in parameters, name in names do
        let mut displayName := name
        if occupied.contains displayName then
          let mut index := 1
          displayName := name.appendIndexAfter index
          while reserved.contains displayName || occupied.contains displayName do
            index := index + 1
            displayName := name.appendIndexAfter index
        occupied := occupied.insert displayName
        context := context.setUserName parameter.fvarId! displayName
      Meta.withLCtx' context <| action (mkAppN target parameters)

-- Re-elaboration may register metadata or synthesize declarations; keep the check isolated.
private def validVisibleProblem (declName : Name) (view : Morew.Syntax.ProblemView) :
    CommandElabM Bool :=
  liftTermElabM do
    let saved ← Term.saveState
    try
      Term.withoutErrToSorry do
        modifyThe Core.State fun state => { state with messages := {} }
        withPrintParameters declName view fun expected => do
          let expectedType ← Meta.inferType expected
          let expected ← if (← getConstInfo declName).hasValue then pure expected else do
            -- Imported opaque declarations expose their checked reconstruction metadata,
            -- even when reduction of the declaration itself is unavailable.
            let env ← getEnv
            let term ← match Morew.Syntax.getProblemCheckedTerm? env declName with
              | some term => pure term
              | none =>
                if (Morew.Syntax.getProblemCheckedView? env declName).isSome then
                  throwError "missing checked source term"
                let some exact := Morew.Syntax.getProblemView? env declName
                  | throwError "missing problem reconstruction metadata"
                pure (← liftMacroM exact.toTermSyntax).raw
            let reconstructed ← Term.elabTermEnsuringType term expectedType
            Term.synthesizeSyntheticMVarsNoPostponing
            let reconstructed ← instantiateMVars reconstructed
            if reconstructed.hasMVar || reconstructed.hasLevelMVar || reconstructed.hasSorry then
              throwError "problem reconstruction contains unresolved terms"
            pure reconstructed
          let printed ← formatProblemView view
          let visible ← match Parser.runParserCategory (← getEnv) `term printed.pretty with
            | .ok visible => pure visible
            | .error _ => return false
          let actual ← Term.elabTermEnsuringType visible expectedType
          Term.synthesizeSyntheticMVarsNoPostponing
          let actual ← instantiateMVars actual
          if (← getThe Core.State).messages.hasErrors || actual.hasMVar ||
              actual.hasLevelMVar || actual.hasSorry then return false
          Meta.isDefEq actual expected
    catch exception =>
      if exception.isInterrupt || exception.isMaxRecDepth || exception.isMaxHeartbeat then
        throw exception
      return false
    finally
      saved.restore (restoreInfo := true)
      setEnv saved.meta.core.env

private partial def freezePrintReferences (infos : SubExpr.PosMap Elab.Info)
    (stx : Lean.Syntax) : Lean.Syntax :=
  if let .ident (.synthetic start _ _) _ _ _ := stx then
    let expression? := match infos.get? start.byteIdx with
      | some (.ofTermInfo info) => some info.expr
      | some (.ofDelabTermInfo info) => some info.expr
      | _ => none
    if let some (.const name _) := expression? then
      mkCIdentFrom stx name
    else stx
  else stx.setArgs (stx.getArgs.map (freezePrintReferences infos))

private partial def qualifyPrintSyntax (locals : NameSet) (inlinePrivate : Bool)
    (expanded : NameSet) : Lean.Syntax → TermElabM Lean.Syntax
  | stx@(.ident info _ name resolved) =>
      if locals.contains name.eraseMacroScopes then pure stx
      else match resolved with
        | [.decl declaration []] => do
            let candidates ← resolveGlobalName name.eraseMacroScopes (enableLog := false)
            if candidates == [(declaration, [])] then return stx
            let name := privateToUserName declaration
            let candidates ← resolveGlobalName name (enableLog := false)
            if inlinePrivate && isPrivateName declaration &&
                candidates != [(declaration, [])] && !expanded.contains declaration then
              if let some value := (← getConstInfo declaration).value? then
                -- Exported replay helpers can retain bodies without acquiring a public
                -- spelling. Inline them only in the checked exact fallback.
                let (body, infos) ← withOptions (fun options => options
                    |>.setBool `pp.all true |>.setBool `pp.universes false
                    |>.setBool `pp.proofs true |>.setBool `pp.structureInstances false) <|
                  PrettyPrinter.delabCore value {} PrettyPrinter.Delaborator.delab
                return ← qualifyPrintSyntax locals true (expanded.insert declaration)
                  (freezePrintReferences infos body.raw)
            let name := if candidates == [(declaration, [])] then name else `_root_ ++ name
            return .ident info name.toString.toRawSubstring name resolved
        | _ => pure stx
  | source@(.node info kind children) => do
      -- A projection field is resolved from its receiver, not as a standalone global name.
      if kind == ``Parser.Term.proj then
        return source.setArg 0 (← qualifyPrintSyntax locals inlinePrivate expanded source[0])
      return .node info kind (← children.mapM (qualifyPrintSyntax locals inlinePrivate expanded))
  | stx => pure stx

private def qualifiedPrintView (declName : Name) (view : Morew.Syntax.ProblemView)
    (inlinePrivate := false) :
    CommandElabM Morew.Syntax.ProblemView :=
  liftTermElabM do
    withPrintParameters declName view fun _ => do
      let locals := (← getLCtx).foldl (fun names declaration =>
        names.insert declaration.userName.eraseMacroScopes) ({} : NameSet)
      let locals := (view.binders.map (·.name) ++ view.definitions.map (·.name)).foldl
        (fun names name => names.insert name.eraseMacroScopes) locals
      let qualify := qualifyPrintSyntax locals inlinePrivate {}
      return { view with
        binders := ← view.binders.mapM fun binder => do
          return { binder with typeSyntax := ← qualify binder.typeSyntax }
        definitions := ← view.definitions.mapM fun definition => do
          return { definition with
            typeSyntax? := ← definition.typeSyntax?.mapM qualify
            inferredTypeSyntax? := ← definition.inferredTypeSyntax?.mapM qualify
            value := ← qualify definition.value }
        objective := ← qualify view.objective
        constraints := ← view.constraints.mapM fun constraint => do
          return { constraint with proposition := ← qualify constraint.proposition } }

private partial def differsOnlyByProofOmissions (compact detailed : Lean.Syntax) : Bool :=
  if compact.isOfKind ``Parser.Term.omission then true
  else match compact, detailed with
    | .node _ leftKind left, .node _ rightKind right =>
        leftKind == rightKind && left.size == right.size &&
          (left.zip right).all fun (left, right) => differsOnlyByProofOmissions left right
    | .ident _ _ left _, .ident _ _ right _ => left == right
    | .atom _ left, .atom _ right => left == right
    | .missing, .missing => true
    | _, _ => false

private def validCompactShape (compact detailed : Morew.Syntax.ProblemView) : CoreM Bool := do
  let compact ← formatProblemView compact
  let detailed ← formatProblemView detailed
  let .ok compact := Parser.runParserCategory (← getEnv) `term compact.pretty | return false
  let .ok detailed := Parser.runParserCategory (← getEnv) `term detailed.pretty | return false
  return differsOnlyByProofOmissions compact detailed

private def qualifiedPrintRows (declName : Name) (view : Morew.Syntax.ProblemView)
    (rows : Array (Option Morew.Syntax.PowerChainRow)) :
    CommandElabM (Array (Option Morew.Syntax.PowerChainRow)) :=
  liftTermElabM do
    withPrintParameters declName view fun _ => do
      let locals := (← getLCtx).foldl (fun names declaration =>
        names.insert declaration.userName.eraseMacroScopes) ({} : NameSet)
      let locals := (view.binders.map (·.name) ++ view.definitions.map (·.name)).foldl
        (fun names name => names.insert name.eraseMacroScopes) locals
      let qualify := qualifyPrintSyntax locals false {}
      rows.mapM fun row => row.mapM fun
        | .first auxiliary source membership =>
            return .first (← qualify auxiliary) (← qualify source) membership
        | .step auxiliary source index size =>
            return .step (← qualify auxiliary) (← qualify source) index (← qualify size)
        | .nonneg auxiliary last membership =>
            return .nonneg (← qualify auxiliary) (← qualify last) membership
        | .bound value auxiliary last membership =>
            return .bound (← qualify value) (← qualify auxiliary) (← qualify last) membership
        | .inverse value auxiliary last exponent =>
            return .inverse (← qualify value) (← qualify auxiliary) (← qualify last)
              (← qualify exponent)

private def refreshMathematicalRows (declName : Name) (view : Morew.Syntax.ProblemView)
    (presentation : Morew.Syntax.ProblemPrintPresentation) :
    CommandElabM Morew.Syntax.ProblemPrintPresentation := do
  unless presentation.mathematicalRows.any Option.isSome do return presentation
  unless (← getConstInfo declName).hasValue do
    return { presentation with
      mathematicalRows := ← qualifiedPrintRows declName view presentation.mathematicalRows }
  match problemPrintAttribute.getValues (← getEnv) `presentation with
  | [renderer] =>
      let refreshed ← renderer.refresh declName view
      return { presentation with mathematicalRows := refreshed.mathematicalRows }
  | _ =>
      return { presentation with
        mathematicalRows := ← qualifiedPrintRows declName view presentation.mathematicalRows }

/-- Select a cached presentation only while its visible spelling remains valid in this scope. -/
def currentProblemPrintPresentation (declName : Name) :
    CommandElabM Morew.Syntax.ProblemPrintPresentation := do
  let env ← getEnv
  let some display := Morew.Syntax.getProblemDisplayView? env declName
    | throwError "declaration `{privateToUserName declName}` has no registered problem presentation"
  let cached := (Morew.Syntax.getProblemPrintPresentation? env declName).getD
    { compact := display, detailed := display }
  -- Preserve structural metadata diagnostics before attempting semantic refresh.
  discard <| liftCoreM <| formatProblemView cached.compact cached.mathematicalRows
  if (← validVisibleProblem declName cached.detailed) &&
      (← liftCoreM <| validCompactShape cached.compact cached.detailed) then
    return ← refreshMathematicalRows declName display cached
  let qualified := { cached with
    compact := ← qualifiedPrintView declName cached.compact
    detailed := ← qualifiedPrintView declName cached.detailed
    mathematicalRows := ← qualifiedPrintRows declName cached.compact cached.mathematicalRows }
  if (← validVisibleProblem declName qualified.detailed) &&
      (← liftCoreM <| validCompactShape qualified.compact qualified.detailed) then
    return ← refreshMathematicalRows declName display qualified
  match problemPrintAttribute.getValues env `presentation with
  | [renderer] =>
      if (← getConstInfo declName).hasValue then
        let refreshed ← renderer.refresh declName display
        if ← validVisibleProblem declName refreshed.detailed then return refreshed
        -- A constant-only comparison can otherwise infer Nat or Int instead of its
        -- checked scalar type. Retain readable notation while making its numerals explicit.
        let typed ← withScope (fun scope =>
            { scope with opts := scope.opts.setBool `pp.numericTypes true }) <|
          renderer.refresh declName display
        if ← validVisibleProblem declName typed.detailed then return typed
      -- Exact reconstruction is also a checked fallback when readable syntax cannot
      -- express the selected instances in the current scope.
      let exact := ((Morew.Syntax.getProblemCheckedView? env declName).or
        (Morew.Syntax.getProblemView? env declName)).getD display
      let exact ← qualifiedPrintView declName exact (inlinePrivate := true)
      if ← validVisibleProblem declName exact then
        return { compact := exact, detailed := exact }
      throwError "cannot render problem `{privateToUserName declName}` in the current scope"
  | [] =>
      let fallback := (Morew.Syntax.getProblemFallbackView? env declName).getD display
      let fallback ← qualifiedPrintView declName fallback
      if ← validVisibleProblem declName fallback then
        return { compact := fallback, detailed := fallback }
      let exact := ((Morew.Syntax.getProblemCheckedView? env declName).or
        (Morew.Syntax.getProblemView? env declName)).getD display
      let exact ← qualifiedPrintView declName exact (inlinePrivate := true)
      if ← validVisibleProblem declName exact then
        return { compact := exact, detailed := exact }
      throwError "cannot render problem `{privateToUserName declName}` in the current scope"
  | _ => throwError "multiple internal problem presentation renderers registered"

/-- Elaborate `#printp` by retrieving and formatting stored presentation metadata. -/
@[command_elab printProblemCmd]
def elabPrintProblem : CommandElab := fun stx => do
  let `(#printp $name:ident) := stx | throwUnsupportedSyntax
  let declName ← resolveGlobalConstNoOverload name
  let env ← getEnv
  let some _ := Morew.Syntax.getProblemDisplayView? env declName
    | throwErrorAt name "declaration `{privateToUserName declName}` has no registered problem presentation"
  -- A nested `problem` term can register metadata for its enclosing declaration.
  -- Check the declaration's result type, reducing aliases and parameters.
  let isProblem ← liftTermElabM do
    let info ← getConstInfo declName
    Lean.Meta.forallTelescopeReducing info.type
      (fun _ resultType => pure <| resultType.isAppOfArity ``Morew.Problem 2)
      (whnfType := true)
  unless isProblem do
    throwErrorAt name
      "declaration `{privateToUserName declName}` has problem presentation metadata but is not a `Morew.Problem`"
  let presentation ← currentProblemPrintPresentation declName
  let (view, mathematicalRows) := if getPPProofs (← getOptions) then
      (presentation.detailed, #[])
    else (presentation.compact, presentation.mathematicalRows)
  logInfoAt stx (← liftCoreM <| formatProblemView view mathematicalRows)

end Morew
