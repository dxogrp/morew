/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Replace
import Morew.Elab.Reformulation.View
import Lean.Meta.Closure

/-! Construct replacement and added constraints, storing their names, certificates,
and reference problems. -/

namespace Morew.Elab.Reformulation.Rows

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

/-- Naming and diagnostic conventions of a replacement command. -/
structure Style where
  /-- Generated-row marker and shared-proof prefix, such as `conic` or `nlp`. -/
  family : String
  /-- Command spelling used in internal allocation diagnostics. -/
  diagnostic : String
  /-- Kind used for the stored primitive certificate declaration. -/
  certificateKind : Name

/-- Find a current label without resolving it as a global declaration. -/
def findConstraint (state : ReformState) (selector : TSyntax `ident) : CommandElabM Nat := do
  let some index := state.view.constraints.findIdx? fun constraint =>
      sameVisibleName constraint.name selector.getId
    | throwErrorAt selector "unknown or stale constraint label `{selector.getId.eraseMacroScopes}`"
  return index

/-- Resolve parameterized declarations for inference from the selected constraint.
Elaborate closed records and certificate expressions as terms, without registry fallback. -/
def elaborateRule (selector : TSyntax `ident) (rule? : Option (TSyntax `term)) :
    TermElabM (Option Expr × Option Name) := do
  let some ruleSyntax := rule? | return (none, none)
  try
    if ruleSyntax.raw.isIdent then
      if let some expression@(.const name _) ← resolveId? ruleSyntax (withInfo := true) then
        if (← whnf (← inferType expression)).isForall then
          return (none, some name)
    let rule ← elabTerm ruleSyntax none
    synthesizeSyntheticMVarsNoPostponing
    let rule ← instantiateMVars rule
    if rule.hasMVar then throwError "exact rule contains unresolved metavariables"
    return (some rule, none)
  catch
    | .error _ message =>
      throwErrorAt ruleSyntax
        "constraint `{selector.getId.eraseMacroScopes}`: failed to elaborate exact rule: {message}"
    | exception => throw exception

/-- Decode the final user-visible component used by generated name families. -/
def generatedStem (selector : TSyntax `ident) : CommandElabM String := do
  let .str _ stem := selector.getId.eraseMacroScopes
    | throwErrorAt selector "cannot derive a generated-name family from constraint `{selector.getId}`"
  if stem.isEmpty then
    throwErrorAt selector "cannot derive a generated-name family from an empty constraint label"
  return stem

/-- Request one optional auxiliary and ordered rows; allocation remains with the runner. -/
def nameRequests (style : Style) (selector : TSyntax `ident)
    (hasAuxiliary : Bool) (rowCount : Nat) : CommandElabM (Array NameRequest) := do
  let stem ← generatedStem selector
  let mut requests := #[]
  if hasAuxiliary then
    requests := requests.push {
      id := 0, kind := .generatedBinderFamily
      requested := Name.mkSimple (stem ++ "_aux"), ref := selector.raw
    }
  for i in [:rowCount] do
    requests := requests.push {
      id := i + 1, kind := .generatedRowFamily
      requested := Name.mkSimple s!"{stem}_{style.family}_{i + 1}", ref := selector.raw
    }
  return requests

/-- Share repeated rows, certificates, and problems in stored proof data. -/
partial def shareCertificate (certificate : Expr)
    (candidates : List (Name × Expr)) : MetaM Expr := do
  match candidates with
  | [] => pure certificate
  | (name, value) :: remaining =>
    withLetDecl name (← inferType value) value fun binding => do
      let replace := fun expression : Expr => expression.replace fun subexpression =>
        if subexpression == value then some binding else none
      let body ← shareCertificate (replace certificate)
        (remaining.map fun (name, value) => (name, replace value))
      mkLetFVars #[binding] body

/-- Store a kernel-checked certificate with section parameters in the command transaction. -/
def storeCertificate (kind : Name) (certificate : Expr)
    (candidates : List (Name × Expr)) : TermElabM Expr := do
  let certificate ← shareCertificate (← instantiateMVars certificate) candidates
  checkWithKernel certificate
  let name ← mkAuxDeclName (kind := kind)
  let certificate ← mkAuxDefinitionFor name certificate (zetaDelta := true) (compile := false)
  modifyEnv (addNoncomputable · name)
  return certificate

/-- A validated replacement in the current term elaboration context. -/
structure Materialization where
  /-- Optional decision coordinates appended by the replacement. -/
  auxiliary? : Option Expr
  /-- Decision space of the checked target. -/
  nextDomain : Expr
  /-- Precisely the generated predicates, in display order. -/
  rowPredicates : Array Expr
  /-- Planner certificate to share in the stored equivalence. -/
  certificate : Expr
  /-- Target problem and checked equivalence assembled by the typed replacement engine. -/
  replacement : Morew.Elab.Reformulation.Replace.RewriteResult

/-- Emit one selected-row replacement after its command-specific checks have passed. -/
def finish (style : Style) (state : ReformState) (typed : RunnerState) (index : Nat)
    (data : Materialization) (allocation : NameAllocation) : TermElabM SurfaceStepResult := do
  let replacement := data.replacement
  let exact ← mkAppM ``Morew.GlobalEquiv.trans
    #[typed.normalization.equiv, replacement.equiv]
  let primitive ← state.runner.liftEquiv exact
  let predicates := typed.presentation.constraints.map (·.predicate) ++ data.rowPredicates
  let candidates := predicates.toList.zipIdx.map fun (predicate, index) =>
    (Name.mkSimple s!"{style.family}_row_{index}", predicate)
  let primitive ← storeCertificate style.certificateKind primitive (candidates ++ [
    (Name.mkSimple (style.family ++ "_certificate"), data.certificate),
    (Name.mkSimple (style.family ++ "_source"), typed.canonical),
    (Name.mkSimple (style.family ++ "_target"), replacement.targetProblem)])
  let mut binders := state.view.binders
  if let some auxiliary := data.auxiliary? then
    let some name := allocation.findName? 0
      | throwError "internal error: missing {style.diagnostic} auxiliary allocation"
    let name ← withFreshMacroScope do MonadQuotation.addMacroScope name
    binders := binders.push { name, typeSyntax := ← presentationTypeSyntax auxiliary }
  let mut rows := #[]
  for i in [:data.rowPredicates.size] do
    let some name := allocation.findName? (i + 1)
      | throwError "internal error: missing {style.diagnostic} row allocation"
    rows := rows.push { name, proposition := (← `(True)).raw : Morew.Syntax.ConstraintView }
  let originalTypes := typed.presentation.binders.map (·.type)
  let binderTypes := match data.auxiliary? with
    | none => originalTypes
    | some auxiliary => originalTypes.push auxiliary
  let declarations := binders.mapIdx fun i binder => (binder.name, binderTypes[i]!)
  let renderedRows ← withLocalDeclsDND declarations fun decisions => do
    let point ← packPoint decisions
    let names := decisions.mapIdx fun i decision => (decision.fvarId!, binders[i]!.name)
    rows.mapIdxM fun i row => do
      -- Reduce generated structure while retaining untouched row syntax.
      let body ← dsimpPreservingProofLets (mkApp data.rowPredicates[i]! point)
      pure { row with proposition := ← delabPresentationTerm body names }
  let view := {
    state.view with
    binders
    constraints := state.view.constraints.extract 0 index ++ renderedRows ++
      state.view.constraints.extract (index + 1) state.view.constraints.size
  }
  let semantic ← exactExpressionSyntax (← simpOnly replacement.targetProblem
    (preserveProofLets := true))
  return {
    view
    semantic
    semanticDomainType := ← exactExpressionSyntax data.nextDomain
    primitiveCertificate := ← exactExpressionSyntax primitive
    simplifyExpLogTerms := state.simplifyExpLogTerms
    hasSubstitution := state.hasSubstitution
    liveCheckpointRows := Array.range view.constraints.size
    removedCheckpointRows := {}
    normalizationLemmas := state.normalizationLemmas
    checkpoint? := some { semantic, semanticAnchor := semantic, view }
    constraintSplices := #[{ index, count := rows.size }]
  }

end Morew.Elab.Reformulation.Rows

namespace Morew.Elab.Reformulation.Rows.Append

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

/-- Diagnostics and stored-certificate names for a constraint-adding step. -/
structure Style where
  /-- Description used when elaborating the proposed predicate. -/
  description : String
  /-- Kind of the auxiliary declaration storing the primitive certificate. -/
  certificateKind : Name
  /-- Prefix of shared expressions within the stored certificate. -/
  family : String

private partial def pointComponents (point : Expr) : Nat → MetaM (Array Expr)
  | 0 => pure #[]
  | 1 => pure #[point]
  | n + 2 => do
      let first ← mkAppM ``Prod.fst #[point]
      let last ← mkAppM ``Prod.snd #[point]
      return (← pointComponents first (n + 1)).push last

/-- Elaborate a supplied constraint certificate, reject incomplete terms, and kernel-check
it after instantiating metavariables in the local context. -/
def elaborateProof (provided : TSyntax `term) (expected : Expr) (description : String) :
    TermElabM Expr := withRef provided do
  let proof ← elabTermEnsuringType provided expected
  synthesizeSyntheticMVarsNoPostponing
  if (← getThe Core.State).messages.hasErrors then throwAbortTerm
  let proof ← instantiateMVars proof
  if proof.hasMVar || proof.hasSorry then
    throwError "{description} contains unresolved metavariables or placeholders"
  withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
    checkWithKernel proof
  pure proof

/-- Close the proposed row over current model bindings before checking its semantic certificate. -/
def elaboratePredicate (style : Style) (state : ReformState)
    (typed : Morew.Elab.Reformulation.RunnerState) (proposition : TSyntax `term) :
    TermElabM (Expr × Syntax) :=
  withPresentationBinders typed.presentation fun _ binders =>
    withViewDefinitions state.view fun definitions => do
      let body ← elabPresentationTerm proposition (binders ++ definitions)
        (some (mkSort .zero))
      if (← getThe Core.State).messages.hasErrors then throwAbortTerm
      if body.hasMVar || body.hasSorry then
        throwErrorAt proposition
          "{style.description} contains unresolved metavariables or placeholders"
      unless ← isDefEq (← inferType body) (mkSort .zero) do
        throwErrorAt proposition "a {style.description} must be a proposition"
      let names := binders.mapIdx (fun i binding =>
        (binding.fvarId!, state.view.binders[i]!.name)) ++
        definitions.mapIdx (fun i binding =>
          (binding.fvarId!, state.view.definitions[i]!.name))
      let propositionSyntax ← delabPresentationTerm body names
      let body ← mkLetFVars definitions body (usedLetOnly := false)
      let predicate ← withLocalDeclD `point typed.semanticDomainType fun point => do
        let components ← pointComponents point binders.size
        mkLambdaFVars #[point] (body.replaceFVars binders components)
      return (predicate, propositionSyntax)

/-- Add a certified constraint and retain the resulting problem, constraint order, and labels. -/
def finish (style : Style) (state : ReformState)
    (typed : Morew.Elab.Reformulation.RunnerState) (name : Name)
    (proposition : TSyntax `term) (predicate : Expr) (propositionSyntax : Syntax)
    (addition : Expr) : TermElabM SurfaceStepResult := do
  let natural ← mkAppM ``Morew.Problem.addConstraint #[typed.semantic, predicate]
  let presentation := { typed.presentation with
    constraints := typed.presentation.constraints.push {
      name, predicate, ref := proposition.raw } }
  let next ← presentation.canonicalProblem
  let feasibleIff ← withLocalDeclD `point typed.semanticDomainType fun point => do
    let unchanged ← mkAppM ``Iff.refl #[mkApp predicate point]
    let normalized ← mkAppM ``and_congr
      #[mkApp typed.normalization.feasibleIff point, unchanged]
    let currentFeasible ← mkAppM ``Morew.Problem.feasible #[typed.canonical, point]
    let nextFeasible ← mkAppM ``Morew.Problem.feasible #[next, point]
    let appended := mkApp2 (mkConst ``And) currentFeasible (mkApp predicate point)
    let reassociationType := mkApp2 (mkConst ``Iff) appended nextFeasible
    let reassociation ← elabTermEnsuringType
      (← `(by simp only [and_assoc, true_and])) reassociationType
    synthesizeSyntheticMVarsNoPostponing
    let reassociation ← instantiateMVars reassociation
    mkLambdaFVars #[point] (← mkAppM ``Iff.trans #[normalized, reassociation])
  let normalization ← mkAppM ``Morew.pointwiseEquiv
    #[natural, next, typed.normalization.objectiveEquality, feasibleIff]
  let exact ← mkAppM ``Morew.GlobalEquiv.trans #[addition, normalization]
  let primitive ← state.runner.liftEquiv exact
  let primitive ← withLCtx' (← instantiateLCtxMVars (← getLCtx)) do
    Rows.storeCertificate style.certificateKind primitive [
      (Name.mkSimple (style.family ++ "_constraint"), predicate),
      (Name.mkSimple (style.family ++ "_source"), typed.semantic),
      (Name.mkSimple (style.family ++ "_target"), next)]
  let view := { state.view with
    constraints := state.view.constraints.push { name, proposition := propositionSyntax } }
  let semantic ← exactExpressionSyntax next
  return {
    view
    semantic
    semanticDomainType := state.semanticDomainType
    primitiveCertificate := ← exactExpressionSyntax primitive
    simplifyExpLogTerms := state.simplifyExpLogTerms
    hasSubstitution := state.hasSubstitution
    liveCheckpointRows := Array.range view.constraints.size
    removedCheckpointRows := {}
    normalizationLemmas := state.normalizationLemmas
    checkpoint? := some { semantic, semanticAnchor := semantic, view }
  }

end Morew.Elab.Reformulation.Rows.Append
