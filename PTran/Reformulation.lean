import PTran.Transform
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reformulation command

This module implements the small, proof-producing transformation language used
by PTran's first release.  A reformulation command declares both the transformed
problem and a `GlobalEquivalence` certificate.  Convexity is deliberately not
part of either the command or the generated proof.
-/

namespace PTran

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

/-- Syntax category for one proof-producing reformulation step. -/
declare_syntax_cat reformulationStep

/-- Substitute a decision variable with a parameterization, optionally using
an explicit feasible-surjection certificate. -/
syntax (name := substituteStep)
  "substitute " ident " := " term (" using " term)? : reformulationStep
/-- Introduce an epigraph variable for a minimization objective. -/
syntax (name := epigraphStep) "epigraph " ident : reformulationStep
/-- Introduce a hypograph variable for a maximization objective. -/
syntax (name := hypographStep) "hypograph " ident : reformulationStep

/-- Declare a transformed problem together with its global-equivalence
certificate. -/
syntax (name := reformulationCmd)
  "reformulation" ident "/" ident ":" ident ":=" "by" ppLine
    ppIndent(reformulationStep*) : command

private def sameUserName (a b : Name) : Bool :=
  a.eraseMacroScopes == b.eraseMacroScopes

private partial def replaceIdent (stx : Lean.Syntax) (oldName : Name)
    (replacement : Lean.Syntax) : Lean.Syntax :=
  if stx.isIdent && sameUserName stx.getId oldName then
    replacement
  else
    stx.setArgs (stx.getArgs.map fun child => replaceIdent child oldName replacement)

private partial def simplifyExpLog (stx : Lean.Syntax) : MacroM Lean.Syntax := do
  let args ← stx.getArgs.mapM simplifyExpLog
  let simplified := stx.setArgs args
  match simplified with
  | `(term| Real.log $logArgument:term) =>
      match logArgument with
      | `(term| Real.exp $argument:term) => simplifyExpLog argument
      | _ => pure simplified
  | `(term| 0 < Real.exp $_argument:term) =>
      `(True)
  | `(term| ($inner:term)) =>
      if inner.raw.isIdent then pure inner.raw else pure simplified
  | _ => pure simplified

private def isTrueSyntax (stx : Lean.Syntax) : Bool :=
  match stx with
  | `(True) => true
  | _ => false

private def isPositiveConstraintFor (constraint : PTran.Syntax.ConstraintView)
    (name : Name) : Bool :=
  match constraint.proposition with
  | `(term| 0 < $varIdent:ident) => sameUserName varIdent.getId name
  | _ => false

private def mkProductType (types : Array Lean.Syntax) : MacroM (TSyntax `term) := do
  if h : types.size > 0 then
    let first : TSyntax `term := ⟨types[0]⟩
    let mut result := first
    for i in [1:types.size] do
      let next : TSyntax `term := ⟨types[i]!⟩
      result ← `($result × $next)
    pure result
  else
    Macro.throwError "a reformulated problem must have at least one decision variable"

private def mkProduct (terms : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  if h : terms.size > 0 then
    let mut result := terms[0]
    for i in [1:terms.size] do
      result ← `(⟨$result, $(terms[i]!)⟩)
    pure result
  else
    Macro.throwError "a reformulated problem must have at least one decision variable"

private def mkProductPattern (names : Array Name) : MacroM (TSyntax `term) := do
  let terms := names.map fun name => (⟨mkIdent name⟩ : TSyntax `term)
  mkProduct terms

private def mkConstraintEvidence (point : TSyntax `term) (index count : Nat) :
    MacroM (TSyntax `term) := do
  let mut evidence ← `(($point).2)
  for _ in [:index] do
    evidence ← `(($evidence).2)
  if index + 1 < count then
    evidence ← `(($evidence).1)
  pure evidence

private partial def collectIdents (stx : Lean.Syntax) (result : NameSet := {}) : NameSet :=
  if stx.isIdent then
    result.insert stx.getId.eraseMacroScopes
  else
    stx.getArgs.foldl (fun result child => collectIdents child result) result

private def inferNewBinder (view : PTran.Syntax.ProblemView) (oldName : Name)
    (replacement : Lean.Syntax) : CommandElabM Name := do
  let localNames : NameSet := view.binders.foldl
    (fun names binder => names.insert binder.name.eraseMacroScopes) ({} : NameSet)
  let env ← getEnv
  let candidates := (collectIdents replacement).toList.filter fun name =>
    !sameUserName name oldName && !localNames.contains name && !env.contains name
  match candidates with
  | [name] => pure name
  | [] =>
      throwErrorAt replacement
        "cannot determine the new decision variable; the substitution expression must contain one new identifier"
  | _ =>
      throwErrorAt replacement
        "ambiguous substitution: expected exactly one new decision variable, found {candidates}"

private def objectiveValueTypeSyntax (sourceName : Name) : CommandElabM Lean.Syntax :=
  liftTermElabM do
    let source ← mkConstWithFreshMVarLevels sourceName
    let type ← whnf (← inferType source)
    unless type.getAppFn.isConstOf ``PTran.Problem && type.getAppNumArgs == 2 do
      throwError "declaration `{sourceName}` does not have type `PTran.Problem _ _`"
    let valueType := type.getArg! 1
    let valueType ← whnf valueType
    return (← PrettyPrinter.delab valueType).raw

/-- The command engine only needs the algebraic interface of a certificate
relation.  Keeping these operations as data leaves the runner open to a future
one-way relaxation relation without a closed enumeration of certificate
kinds.  Primitive v1 steps produce global equivalences; `liftEquivalence?`
names the explicit lift into the selected relation when one is required. -/
private structure CertificateRunner where
  relation : Name
  refl : Name
  trans : Name
  liftEquivalence? : Option Name := none

private def namedTerm (name : Name) : TSyntax `term :=
  ⟨mkIdent name⟩

private def CertificateRunner.relationTerm (runner : CertificateRunner)
    (source target : TSyntax `term) : MacroM (TSyntax `term) := do
  let relation := namedTerm runner.relation
  `($relation $source $target)

private def CertificateRunner.reflTerm (runner : CertificateRunner)
    (optimizationProblem : TSyntax `term) : MacroM (TSyntax `term) := do
  let refl := namedTerm runner.refl
  `($refl $optimizationProblem)

private def CertificateRunner.transTerm (runner : CertificateRunner)
    (left right : TSyntax `term) : MacroM (TSyntax `term) := do
  let trans := namedTerm runner.trans
  `($trans $left $right)

private def CertificateRunner.liftEquivalence (runner : CertificateRunner)
    (certificate : TSyntax `term) : MacroM (TSyntax `term) := do
  match runner.liftEquivalence? with
  | none => pure certificate
  | some liftName =>
      let lift := namedTerm liftName
      `($lift $certificate)

private def globalEquivalenceRunner : CertificateRunner where
  relation := ``PTran.GlobalEquivalence
  refl := ``PTran.GlobalEquivalence.refl
  trans := ``PTran.GlobalEquivalence.trans

private structure ReformState where
  view : PTran.Syntax.ProblemView
  semantic : TSyntax `term
  certificate : TSyntax `term
  source : TSyntax `term
  sourceName : Name
  runner : CertificateRunner

private def findBinderIndex (view : PTran.Syntax.ProblemView) (name : Name) : Option Nat :=
  view.binders.findIdx? fun binder => sameUserName binder.name name

private def ensureFreshBinder (view : PTran.Syntax.ProblemView) (name : Name)
    (ref : Lean.Syntax) : CommandElabM Unit := do
  if view.binders.any fun binder => sameUserName binder.name name then
    throwErrorAt ref "decision variable `{name.eraseMacroScopes}` already exists"

private def applySubstitution (state : ReformState) (step : Lean.Syntax)
    (oldIdent : TSyntax `ident) (replacement : TSyntax `term)
    (providedCertificate? : Option (TSyntax `term)) : CommandElabM ReformState := do
  let oldName := oldIdent.getId
  let some binderIndex := findBinderIndex state.view oldName
    | throwErrorAt oldIdent "unknown decision variable `{oldName.eraseMacroScopes}`"

  let newName ← inferNewBinder state.view oldName replacement
  ensureFreshBinder state.view newName replacement

  let oldBinder := state.view.binders[binderIndex]!
  let newBinders := state.view.binders.set! binderIndex {
    oldBinder with name := newName
  }

  let binderNames := newBinders.map fun binder => binder.name
  let binderTypes := newBinders.map fun binder => binder.typeSyntax
  let domainType ← liftMacroM <| mkProductType binderTypes
  let domainPattern ← liftMacroM <| mkProductPattern binderNames
  let mapComponents : Array (TSyntax `term) := state.view.binders.mapIdx fun i binder =>
    if i == binderIndex then replacement else ⟨mkIdent binder.name⟩
  let mapResult ← liftMacroM <| mkProduct mapComponents
  let mapTerm ← liftMacroM `(fun ($domainPattern : $domainType) => $mapResult)

  let objective ← liftMacroM <|
    simplifyExpLog (replaceIdent state.view.objective oldName replacement)
  let mut constraints : Array PTran.Syntax.ConstraintView := #[]
  for constraint in state.view.constraints do
    let proposition ← liftMacroM <|
      simplifyExpLog (replaceIdent constraint.proposition oldName replacement)
    unless isTrueSyntax proposition do
      constraints := constraints.push { constraint with proposition }
  let newView : PTran.Syntax.ProblemView := {
    state.view with
    binders := newBinders
    objective
    constraints
  }

  let stepCertificate ← match providedCertificate? with
    | some certificate => pure certificate
    | none => do
        unless state.semantic.raw == state.source.raw do
          throwErrorAt step
            "the automatic `Real.exp` rule must be the first reformulation step; provide `using` with a `FeasibleSurjection` certificate"
        unless state.view.binders.size == 1 && binderIndex == 0 do
          throwErrorAt step
              "automatic `Real.exp` substitution currently requires a single-variable problem; provide `using` with a `FeasibleSurjection` certificate"
        let some positiveIndex := state.view.constraints.findIdx?
            (fun constraint => isPositiveConstraintFor constraint oldName)
          | throwErrorAt step
              "the registered exponential rule requires the source constraint `0 < {oldName.eraseMacroScopes}`; provide `using` for a more general feasible domain"
        let `(Real.exp $argument:term) := replacement
          | throwErrorAt replacement
              "no registered substitution rule matches this expression; provide `using` with a `FeasibleSurjection` certificate"
        unless argument.raw.isIdent && sameUserName argument.raw.getId newName do
          throwErrorAt replacement
            "the registered exponential rule expects `Real.exp` applied to the new variable"
        let current := state.semantic
        let source := state.source
        let sourceSimp ← liftMacroM `(
          Lean.Parser.Tactic.simpLemma| $source:term)
        let pointIdent : TSyntax `ident := ⟨mkIdent `point⟩
        let pointTerm : TSyntax `term := ⟨pointIdent.raw⟩
        let positiveEvidence ← liftMacroM <|
          mkConstraintEvidence pointTerm positiveIndex state.view.constraints.size
        liftMacroM `(
          ({
            preimage := fun $pointIdent => Real.log ($pointTerm).1
            rightInverse := fun $pointIdent => by
              apply Real.exp_log
              simpa only [$sourceSimp] using $positiveEvidence
          } : PTran.FeasibleSurjection $current $mapTerm))

  let current := state.semantic
  let nextSemantic ← liftMacroM `(PTran.Problem.pullback $current $mapTerm)
  let primitiveEquivalence ← liftMacroM `(
    PTran.pullbackEquivalence $current $mapTerm $stepCertificate)
  let primitive ← liftMacroM <|
    state.runner.liftEquivalence primitiveEquivalence
  let previous := state.certificate
  let nextCertificate ← liftMacroM <|
    state.runner.transTerm previous primitive
  pure {
    state with
    view := newView
    semantic := nextSemantic
    certificate := nextCertificate
  }

private def applyObjectiveBound (state : ReformState) (step : Lean.Syntax)
    (binder : TSyntax `ident) (expectedSense : PTran.Syntax.ObjectiveSense) :
    CommandElabM ReformState := do
  unless state.view.sense == expectedSense do
    let expected := match expectedSense with
      | .minimize => "epigraph"
      | .maximize => "hypograph"
    let actual := match state.view.sense with
      | .minimize => "minimization"
      | .maximize => "maximization"
    throwErrorAt step "`{expected}` is not valid for a {actual} problem"
  let binderName := binder.getId
  ensureFreshBinder state.view binderName binder

  let valueType ← objectiveValueTypeSyntax state.sourceName
  let newBinder : PTran.Syntax.BinderView := {
    name := binderName
    typeSyntax := valueType
  }
  let boundName := mkIdent binderName
  let oldObjective : TSyntax `term := ⟨state.view.objective⟩
  let proposition ← liftMacroM <| match expectedSense with
    | .minimize => `($oldObjective ≤ $boundName)
    | .maximize => `($boundName ≤ $oldObjective)
  let baseName := Name.mkSimple <| match expectedSense with
    | .minimize => s!"epigraph_{binderName.eraseMacroScopes}"
    | .maximize => s!"hypograph_{binderName.eraseMacroScopes}"
  if state.view.constraints.any fun constraint =>
      sameUserName constraint.name baseName then
    throwErrorAt binder
      "generated constraint name `{baseName}` already exists"
  let constraint : PTran.Syntax.ConstraintView := {
    name := baseName
    proposition
  }
  let newView : PTran.Syntax.ProblemView := {
    state.view with
    binders := state.view.binders.push newBinder
    objective := boundName
    constraints := state.view.constraints.push constraint
  }

  let current := state.semantic
  let nextSemantic ← liftMacroM <| match expectedSense with
    | .minimize => `(PTran.Problem.epigraph $current)
    | .maximize => `(PTran.Problem.hypograph $current)
  let primitiveEquivalence ← liftMacroM <| match expectedSense with
    | .minimize => `(PTran.epigraphEquivalence $current)
    | .maximize => `(PTran.hypographEquivalence $current)
  let primitive ← liftMacroM <|
    state.runner.liftEquivalence primitiveEquivalence
  let previous := state.certificate
  let nextCertificate ← liftMacroM <|
    state.runner.transTerm previous primitive
  pure {
    state with
    view := newView
    semantic := nextSemantic
    certificate := nextCertificate
  }

/-- Elaborate a reformulation declaration and emit the transformed problem and
its composed global-equivalence certificate. -/
@[command_elab reformulationCmd]
def elabReformulation : CommandElab := fun stx => do
  let `(reformulation $certificateName:ident / $targetName:ident :
      $sourceIdent:ident := by $steps:reformulationStep*) := stx
    | throwUnsupportedSyntax

  let sourceName ← resolveGlobalConstNoOverload sourceIdent
  let env ← getEnv
  let some sourceView := PTran.Syntax.getProblemView? env sourceName
    | throwErrorAt sourceIdent
        "declaration `{sourceName}` has no registered problem presentation"

  let sourceTerm : TSyntax `term := ⟨sourceIdent.raw⟩
  let runner := globalEquivalenceRunner
  let initialCertificate ← liftMacroM <|
    runner.reflTerm sourceTerm
  let mut state : ReformState := {
    view := sourceView
    semantic := sourceTerm
    certificate := initialCertificate
    source := sourceTerm
    sourceName
    runner
  }

  for step in steps do
    state ← match step with
      | `(reformulationStep| substitute $oldName:ident := $replacement:term
          $[using $provided:term]?) =>
          applySubstitution state step oldName replacement provided
      | `(reformulationStep| epigraph $binder:ident) =>
          applyObjectiveBound state step binder .minimize
      | `(reformulationStep| hypograph $binder:ident) =>
          applyObjectiveBound state step binder .maximize
      | _ => throwUnsupportedSyntax

  let targetTerm ← liftMacroM <| state.view.toTermSyntax
  let targetCommand ← liftMacroM `(
    command| noncomputable def $targetName := $targetTerm)
  elabCommand targetCommand

  let finalSemantic := state.semantic
  let finalPattern ← liftMacroM <|
    mkProductPattern (state.view.binders.map fun binder => binder.name)
  let finalType ← liftMacroM <|
    mkProductType (state.view.binders.map fun binder => binder.typeSyntax)
  let sourceSimp ← liftMacroM `(
    Lean.Parser.Tactic.simpLemma| $sourceTerm:term)
  let targetSimp ← liftMacroM `(
    Lean.Parser.Tactic.simpLemma| $targetName:term)
  let normalizationEquivalence ← liftMacroM `(
    PTran.pointwiseEquivalence $finalSemantic $targetName
      (fun ($finalPattern : $finalType) => by
        simp only [$sourceSimp, $targetSimp, PTran.Problem.pullback,
          PTran.Problem.epigraph, PTran.Problem.hypograph, Real.log_exp,
          Real.exp_pos, true_and, and_true, and_assoc, eq_self, iff_self] <;>
          rfl)
      (fun ($finalPattern : $finalType) => by
        simp only [$sourceSimp, $targetSimp, PTran.Problem.pullback,
          PTran.Problem.epigraph, PTran.Problem.hypograph, Real.log_exp,
          Real.exp_pos, true_and, and_true, and_assoc, eq_self, iff_self] <;>
          rfl))
  let normalization ← liftMacroM <|
    state.runner.liftEquivalence normalizationEquivalence
  let certificate ← liftMacroM <|
    state.runner.transTerm state.certificate normalization
  let relation ← liftMacroM <|
    state.runner.relationTerm sourceTerm ⟨targetName.raw⟩
  let certificateCommand ← liftMacroM `(command|
    noncomputable def $certificateName :
        $relation := by
      exact $certificate)
  elabCommand certificateCommand

end PTran
