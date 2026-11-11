/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Reformulation.Runner

/-! Problem syntax and certificates retained by reformulation commands. -/

namespace Morew.Elab.Reformulation

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

private def namedTerm (name : Name) : TSyntax `term :=
  ⟨mkIdent name⟩

/-- Construct the syntax for a certificate relation. -/
def certificateRelationTerm (runner : CertificateRunner)
    (source target : TSyntax `term) : MacroM (TSyntax `term) := do
  let relation := namedTerm runner.relation
  `($relation $source $target)

/-- Construct the syntax for a reflexive certificate. -/
def certificateReflTerm (runner : CertificateRunner)
    (optimizationProblem : TSyntax `term) : MacroM (TSyntax `term) := do
  let refl := namedTerm runner.refl
  `($refl $optimizationProblem)

/-- Construct the syntax composing two certificates. -/
def certificateTransTerm (runner : CertificateRunner)
    (left right : TSyntax `term) : MacroM (TSyntax `term) := do
  let trans := namedTerm runner.trans
  `($trans $left $right)

/-- Convert an equivalence proof to the selected certificate relation. -/
def liftCertificateEquiv (runner : CertificateRunner)
    (proofTerm : TSyntax `term) : MacroM (TSyntax `term) := do
  match runner.liftEquiv? with
  | none => pure proofTerm
  | some liftName =>
      let lift := namedTerm liftName
      `($lift $proofTerm)

/-- A problem whose ordered rows are preserved during later normalization. -/
structure CanonicalCheckpoint where
  /-- Checked row source supplying the protected objective and ordered rows. -/
  semantic : TSyntax `term
  /-- Problem expression replaced by the stored reference problem during normalization. -/
  semanticAnchor : TSyntax `term
  /-- The stored problem description, with variables and constraints in order. -/
  view : Morew.Syntax.ProblemView

/-- Check that retained and removed constraints partition the stored problem,
with one retained index per displayed constraint in the original order. -/
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

/-- Operations for the selected terminal representation.
Section-dependent expressions are stored in `CheckedTerminalArtifact`. -/
structure TerminalAdapter where
  /-- User-facing representation name. -/
  description : String
  /-- Suffix of the representation declaration. -/
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

/-- Adapt a terminal form with five type arguments ending in its represented problem,
fields `data` and `represents`, and an objective `sense` in its data. The constructor
and representability theorem are `formName.mk` and `formName.propertySuffix`.
Preserve the form's universe levels and stored instances when retargeting it. -/
def TerminalAdapter.ofForm (formName : Name) (formDescription description : String)
    (formSuffix propertySuffix : Name) : TerminalAdapter where
  description := description
  formSuffix := formSuffix
  propertySuffix := propertySuffix
  validate form expected sense := do
    let type ← whnf (← inferType form)
    unless type.isAppOfArity formName 5 do
      throwError "terminal evidence is not a {formDescription}"
    let represented := type.getAppArgs.back!
    unless ← isDefEq represented expected do
      throwError "terminal {description} form does not represent the final canonical problem"
    let data ← mkProjection form `data
    let actualSense ← mkProjection data `sense
    let expectedSense := match sense with
      | .minimize => mkConst ``Morew.ObjectiveSense.minimize
      | .maximize => mkConst ``Morew.ObjectiveSense.maximize
    unless ← isDefEq actualSense expectedSense do
      throwError "terminal {description} form has the wrong objective sense"
    pure represented
  retarget form target equality := do
    let type ← whnf (← inferType form)
    let arguments := type.getAppArgs.set! (type.getAppNumArgs - 1) target
    let represents ← mkAppM ``Eq.trans #[← mkProjection form `represents, equality]
    let data ← mkProjection form `data
    pure <| mkAppN (mkConst (formName ++ `mk) type.getAppFn.constLevels!)
      (arguments ++ #[data, represents])
  property form := do
    let type ← whnf (← inferType form)
    pure <| mkAppN (mkConst (formName ++ propertySuffix) type.getAppFn.constLevels!)
      (type.getAppArgs ++ #[form])

/-- Terminal evidence in the containing state's section-variable context. -/
structure CheckedTerminalArtifact where
  /-- Operations for the selected terminal representation. -/
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
  /-- Current presentation retaining source binding structure. -/
  view : Morew.Syntax.ProblemView
  /-- Syntax describing the current natural semantic problem. -/
  semantic : TSyntax `term
  /-- Stable syntax for the semantic decision domain. -/
  semanticDomainType : TSyntax `term
  /-- Stable syntax for the semantic objective-value type. -/
  semanticValueType : TSyntax `term
  /-- Certificate syntax retaining section binders for declaration emission. -/
  certificateSyntax : TSyntax `term
  /-- Stable syntax referring to the original source problem. -/
  source : TSyntax `term
  /-- Fully qualified declaration name of the source problem. -/
  sourceName : Name
  /-- Outer names used by the current problem and reserved against decision binders.
Certificate-only dependencies do not reserve names. -/
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
  /-- Original positions of the currently displayed constraints in the stored problem. -/
  liveCheckpointRows : Array Nat
  /-- Original positions of constraints proved redundant. -/
  removedCheckpointRows : Std.HashSet Nat := {}
  /-- Checked predicate equivalences retained across successive steps. -/
  normalizationLemmas : Array (TSyntax `term) := #[]
  /-- Structural evidence produced by terminal validation. -/
  terminalArtifact? : Option CheckedTerminalArtifact := none

/-- An uncommitted primitive step; `commitSurfaceStep` composes certificates and updates state. -/
structure SurfaceStepResult where
  /-- Proposed presentation retaining source binding structure. -/
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
  /-- Original positions of the proposed constraints in the stored problem. -/
  liveCheckpointRows : Array Nat
  /-- Original positions of constraints removed in the proposed state. -/
  removedCheckpointRows : Std.HashSet Nat
  /-- Accumulated checked predicate equivalences. -/
  normalizationLemmas : Array (TSyntax `term)
  /-- A new reference problem for normalization, initially with no removed constraints. -/
  checkpoint? : Option CanonicalCheckpoint := none
  /-- Ordered replacements indexed by entries at step entry. -/
  constraintSplices : Array ConstraintSplice := #[]
  /-- Form syntax to validate against the proposed canonical target. -/
  terminalForm? : Option (TerminalAdapter × TSyntax `term) := none
  /-- Whether additional steps may follow this result. -/
  status : Morew.Elab.Reformulation.StepStatus := .continue
  /-- Additional declarations requested by the step. -/
  companions : Array Morew.Elab.Reformulation.CompanionRequest := #[]

/-- A proposed step whose construction waits until its names have been allocated. -/
structure SurfaceStepDraft where
  /-- Names to check and allocate before constructing the step. -/
  nameRequests : Array Morew.Elab.Reformulation.NameRequest
  /-- Build the step using its successfully allocated names. -/
  materialize : Morew.Elab.Reformulation.NameAllocation →
    CommandElabM SurfaceStepResult

/-- The syntax needed to emit a checked typed result. -/
structure SurfaceMaterialization where
  /-- Problem syntax corresponding to the checked result. -/
  surface : SurfaceStepResult
  /-- Section variables used while validating the typed result. -/
  sectionFVars : Array Expr
  /-- Validated terminal evidence in the same section-variable context. -/
  terminalArtifact? : Option CheckedTerminalArtifact := none

end Morew.Elab.Reformulation
