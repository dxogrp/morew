/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Replace
import Morew.Reformulation.Presentation
import Lean.Meta.Closure

/-!
# Surface materialization of selected constraint replacements

Checked planners retain their own recognition and validation policies. This
module handles only names, stored certificates, generated-row presentation,
and the checkpoint for one ordered replacement. The runner still owns name
allocation, transactional declaration emission, and committing the step.
-/

namespace Morew.Reformulation.Internal.Replace

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open Morew.Elab.Reformulation

/-- Existing naming and diagnostic conventions of a replacement command. -/
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
      sameUserName constraint.name selector.getId
    | throwErrorAt selector "unknown or stale constraint label `{selector.getId.eraseMacroScopes}`"
  return index

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

/-- Store a kernel-checked certificate once before the presentation syntax round trip.
The closure retains section parameters; the enclosing command transaction owns rollback. -/
def storeCertificate (kind : Name) (certificate : Expr)
    (candidates : List (Name × Expr)) : TermElabM Expr := do
  let certificate ← shareCertificate (← instantiateMVars certificate) candidates
  checkWithKernel certificate
  let name ← mkAuxDeclName (kind := kind)
  let certificate ← mkAuxDefinitionFor name certificate (zetaDelta := true) (compile := false)
  modifyEnv (addNoncomputable · name)
  return certificate

/-- A validated replacement and the data needed to display and share it.
All expressions already belong to the current term elaboration context. -/
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
  let exact ← mkAppM ``Morew.GlobalEquivalence.trans
    #[typed.normalization.equivalence, replacement.equivalence]
  let primitive ← state.runner.liftEquivalence exact
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
      -- Only generated scaffolding is reduced; untouched row syntax stays in the view.
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
    removedConstraintNames := {}
    normalizationLemmas := state.normalizationLemmas
    checkpoint? := some { semantic, view }
    constraintSplices := #[{ index, count := rows.size }]
  }

end Morew.Reformulation.Internal.Replace
