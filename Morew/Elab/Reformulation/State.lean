/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Runner

/-!
# Surface reformulation state

Shared surface state and certificate syntax. This is an internal implementation API.
-/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

private def namedTerm (name : Name) : TSyntax `term :=
  ⟨mkIdent name⟩

/-- Build the surface syntax for a certificate relation. -/
def certificateRelationTerm (runner : CertificateRunner)
    (source target : TSyntax `term) : MacroM (TSyntax `term) := do
  let relation := namedTerm runner.relation
  `($relation $source $target)

/-- Build the surface syntax for a reflexive certificate. -/
def certificateReflTerm (runner : CertificateRunner)
    (optimizationProblem : TSyntax `term) : MacroM (TSyntax `term) := do
  let refl := namedTerm runner.refl
  `($refl $optimizationProblem)

/-- Build the surface syntax composing two certificates. -/
def certificateTransTerm (runner : CertificateRunner)
    (left right : TSyntax `term) : MacroM (TSyntax `term) := do
  let trans := namedTerm runner.trans
  `($trans $left $right)

/-- Lift an equivalence proof into the selected certificate relation. -/
def liftCertificateEquivalence (runner : CertificateRunner)
    (proofTerm : TSyntax `term) : MacroM (TSyntax `term) := do
  match runner.liftEquivalence? with
  | none => pure proofTerm
  | some liftName =>
      let lift := namedTerm liftName
      `($lift $proofTerm)

/-- The exact problem whose ordered rows are protected while later standard
steps are normalized. A rewrite may establish a new checkpoint without changing
the original source of the accumulated certificate. -/
structure CanonicalCheckpoint where
  /-- Checked row source supplying the protected objective and ordered rows. -/
  semantic : TSyntax `term
  /-- Raw semantic problem replaced by the protected row source when normalizing
  later transformations. Keeping this separate preserves explicit certificates
  against the natural transformation history. -/
  semanticAnchor : TSyntax `term
  /-- The checkpoint's ordered binder and constraint presentation. -/
  view : Morew.Syntax.ProblemView

/-- Check that the internal row inventory is an ordered partition of the
checkpoint, with one live identity for each displayed row. -/
def validateCheckpointRows (checkpointCount rowCount : Nat)
    (live : Array Nat) (removed : Std.HashSet Nat) : Except String Unit := do
  unless live.size == rowCount do
    throw "checkpoint row identities do not align with the displayed rows"
  let mut seen : Std.HashSet Nat := {}
  for position in [:live.size] do
    let index := live[position]!
    unless index < checkpointCount do
      throw "live checkpoint row identity is out of bounds"
    if position > 0 && live[position - 1]! >= index then
      throw "live checkpoint row identities do not preserve checkpoint order"
    if removed.contains index then
      throw "a checkpoint row is both live and removed"
    seen := seen.insert index
  for index in removed do
    unless index < checkpointCount do
      throw "removed checkpoint row identity is out of bounds"
    seen := seen.insert index
  unless seen.size == checkpointCount do
    throw "checkpoint row identities do not cover the checkpoint"

/-- Replace one selected constraint in place by a fixed number of ordered rows.
The index refers to the presentation at step entry. -/
structure ConstraintSplice where
  /-- Position of the selected original constraint. -/
  index : Nat
  /-- Number of generated replacement rows, possibly zero. -/
  count : Nat

/-- Backend-owned operations for terminal evidence. Adapters are static values:
all section-dependent expressions belong to `CheckedTerminalArtifact`. -/
structure TerminalAdapter where
  /-- User-facing representation name. -/
  description : String
  /-- Suffix of the concrete form declaration. -/
  formSuffix : Name
  /-- Suffix of the representability theorem. -/
  propertySuffix : Name
  /-- Validate the form, represented problem, and objective sense; return the
  represented problem from the checked form's type. -/
  validate : Expr → Expr → Morew.ObjectiveSense → TermElabM Expr
  /-- Transport a form along a checked equality to the emitted target. -/
  retarget : Expr → Expr → Expr → TermElabM Expr
  /-- Construct representability evidence from the emitted form. -/
  property : Expr → TermElabM Expr

/-- Checked structural evidence retained until the final target is declared.
Its free variables belong to the containing state's section-variable context. -/
structure CheckedTerminalArtifact where
  /-- Static operations supplied by the selected backend. -/
  adapter : TerminalAdapter
  /-- A kernel-checked form of the final canonical problem. -/
  form : Expr
  /-- The form's represented problem, retained in the same local context. -/
  representedProblem : Expr
  /-- Source location of terminal validation. -/
  ref : Syntax

/-- Move every retained terminal expression into a later elaboration context. -/
def CheckedTerminalArtifact.replaceFVars (artifact : CheckedTerminalArtifact)
    (oldVars newVars : Array Expr) : CheckedTerminalArtifact :=
  { artifact with
    form := artifact.form.replaceFVars oldVars newVars
    representedProblem := artifact.representedProblem.replaceFVars oldVars newVars }

/-- Checked runner state together with syntax retained for declaration emission. -/
structure ReformState where
  /-- Current checked semantic, presentation, and certificate state. -/
  typed : Morew.Elab.Reformulation.RunnerState
  /-- Section variables used by the retained typed expressions. -/
  sectionFVars : Array Expr
  /-- Current source-aligned presentation. -/
  view : Morew.Syntax.ProblemView
  /-- Syntax describing the current natural semantic problem. -/
  semantic : TSyntax `term
  /-- Stable syntax for the semantic decision domain. -/
  semanticDomainType : TSyntax `term
  /-- Stable syntax for the semantic objective-value type. -/
  semanticValueType : TSyntax `term
  /-- Re-elaboratable mirror of the checked typed certificate, retained only
  for command emission so section variables keep their source binders. -/
  certificateSyntax : TSyntax `term
  /-- Stable syntax referring to the original source problem. -/
  source : TSyntax `term
  /-- Fully qualified declaration name of the source problem. -/
  sourceName : Name
  /-- Outer parameter names used by the applied source or introduced into the
  current semantic problem by later steps. Decision binders must avoid these
  names when the presentation is re-elaborated. Certificate-only dependencies
  do not add reservations. -/
  usedSourceParameterNames : Array Name := #[]
  /-- Whether the source presentation was instantiated from an application. -/
  instantiatedSource : Bool := false
  /-- Base problem and row boundaries protected by canonicalization. -/
  checkpoint : CanonicalCheckpoint
  /-- Certificate relation and composition operations. -/
  runner : CertificateRunner
  /-- Whether canonicalization simplifies exponential and logarithmic terms. -/
  simplifyExpLogTerms : Bool := false
  /-- Whether the script has committed a substitution step. -/
  hasSubstitution : Bool := false
  /-- Original checkpoint positions, aligned with the current displayed rows. -/
  liveCheckpointRows : Array Nat
  /-- Checkpoint positions whose rows have been proved removable. -/
  removedCheckpointRows : Std.HashSet Nat := {}
  /-- Checked predicate equivalences retained across successive steps. -/
  normalizationLemmas : Array (TSyntax `term) := #[]
  /-- Structural evidence produced by terminal validation. -/
  terminalArtifact? : Option CheckedTerminalArtifact := none

/-- A handler describes one uncommitted primitive step.  Certificate
composition and state mutation are deliberately centralized in
`commitSurfaceStep`. -/
structure SurfaceStepResult where
  /-- Proposed source-aligned presentation after the step. -/
  view : Morew.Syntax.ProblemView
  /-- Syntax describing the step's natural semantic problem. -/
  semantic : TSyntax `term
  /-- Stable syntax for the proposed decision domain. -/
  semanticDomainType : TSyntax `term
  /-- Certificate from the current semantic problem to the proposed one. -/
  primitiveCertificate : TSyntax `term
  /-- Whether to simplify exponential and logarithmic terms. -/
  simplifyExpLogTerms : Bool
  /-- Whether the proposed state includes a substitution. -/
  hasSubstitution : Bool
  /-- Original checkpoint positions, aligned with the proposed displayed rows. -/
  liveCheckpointRows : Array Nat
  /-- Checkpoint positions removed by the proposed state. -/
  removedCheckpointRows : Std.HashSet Nat
  /-- Accumulated checked predicate equivalences. -/
  normalizationLemmas : Array (TSyntax `term)
  /-- Optional new base for normalization after a checked rewrite. Its removal
  inventory starts empty; subsequent standard steps inherit this checkpoint. -/
  checkpoint? : Option CanonicalCheckpoint := none
  /-- Ordered replacements indexed by entries at step entry. -/
  constraintSplices : Array ConstraintSplice := #[]
  /-- Form syntax to validate against the proposed canonical target. -/
  terminalForm? : Option (TerminalAdapter × TSyntax `term) := none
  /-- Whether additional steps may follow this result. -/
  status : Morew.Elab.Reformulation.StepStatus := .continue
  /-- Additional declarations requested by the step. -/
  companions : Array Morew.Elab.Reformulation.CompanionRequest := #[]

/-- Surface-specific preparation retained around the reusable typed plan.  Its
materializer is not run until the typed name-request batch has passed
preflight. -/
structure SurfaceStepDraft where
  /-- Complete presentation-name batch to preflight before materialization. -/
  nameRequests : Array Morew.Elab.Reformulation.NameRequest
  /-- Build the step using its successfully allocated names. -/
  materialize : Morew.Elab.Reformulation.NameAllocation →
    CommandElabM SurfaceStepResult

/-- The syntax needed to emit a checked typed result. -/
structure SurfaceMaterialization where
  /-- Surface result corresponding to the checked typed result. -/
  surface : SurfaceStepResult
  /-- Section variables used while validating the typed result. -/
  sectionFVars : Array Expr
  /-- Validated terminal evidence in the same section-variable context. -/
  terminalArtifact? : Option CheckedTerminalArtifact := none

end Morew.Elab.Reformulation
