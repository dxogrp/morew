import PTran.Elab.Reformulation

/-!
# Surface reformulation state

Shared surface state and certificate syntax. This is an internal implementation API.
-/

namespace PTran.Reformulation.Internal

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term Lean.Parser

/-- Compare the user-visible spelling of two surface names. -/
def sameUserName (a b : Name) : Bool :=
  a.eraseMacroScopes == b.eraseMacroScopes

/-- Certificate operations selected by the surface runner. -/
abbrev CertificateRunner :=
  PTran.Elab.Reformulation.CertificateRunner

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

/-- The certificate relation used by the public reformulation command. -/
def globalEquivalenceRunner : CertificateRunner :=
  PTran.Elab.Reformulation.globalEquivalenceRunner

/-- Checked runner state together with syntax retained for declaration emission. -/
structure ReformState where
  /-- Current checked semantic, presentation, and certificate state. -/
  typed : PTran.Elab.Reformulation.RunnerState
  /-- Section variables used by the retained typed expressions. -/
  sectionFVars : Array Expr
  /-- Current source-aligned presentation. -/
  view : PTran.Syntax.ProblemView
  /-- Syntax describing the current natural semantic problem. -/
  semantic : TSyntax `term
  /-- Stable syntax for the semantic decision domain. -/
  semanticDomainType : TSyntax `term
  /-- Stable syntax for the semantic objective-value type. -/
  semanticValueType : TSyntax `term
  /-- Objective-value type syntax used in the displayed presentation. -/
  presentationValueType : Lean.Syntax
  /-- Re-elaboratable mirror of the checked typed certificate, retained only
  for command emission so section variables keep their source binders. -/
  certificateSyntax : TSyntax `term
  /-- Stable syntax referring to the original source problem. -/
  source : TSyntax `term
  /-- Fully qualified declaration name of the source problem. -/
  sourceName : Name
  /-- Certificate relation and composition operations. -/
  runner : CertificateRunner
  /-- Whether canonicalization simplifies exponential and logarithmic terms. -/
  simplifyExpLogTerms : Bool := false
  /-- Whether the script has committed a substitution step. -/
  hasSubstitution : Bool := false
  /-- Source constraint labels whose rows have been proved removable. -/
  removedConstraintNames : NameSet := {}
  /-- Checked predicate equivalences retained across successive steps. -/
  normalizationLemmas : Array (TSyntax `term) := #[]

/-- A handler describes one uncommitted primitive step.  Certificate
composition and state mutation are deliberately centralized in
`commitSurfaceStep`. -/
structure SurfaceStepResult where
  /-- Proposed source-aligned presentation after the step. -/
  view : PTran.Syntax.ProblemView
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
  /-- Source constraint labels removed by the proposed state. -/
  removedConstraintNames : NameSet
  /-- Accumulated checked predicate equivalences. -/
  normalizationLemmas : Array (TSyntax `term)
  /-- Whether additional steps may follow this result. -/
  status : PTran.Elab.Reformulation.StepStatus := .continue
  /-- Additional declarations requested by the step. -/
  companions : Array PTran.Elab.Reformulation.CompanionRequest := #[]

/-- Surface-specific preparation retained around the reusable typed plan.  Its
materializer is not run until the typed name-request batch has passed
preflight. -/
structure SurfaceStepDraft where
  /-- Complete presentation-name batch to preflight before materialization. -/
  nameRequests : Array PTran.Elab.Reformulation.NameRequest
  /-- Build the step using its successfully allocated names. -/
  materialize : PTran.Elab.Reformulation.NameAllocation →
    CommandElabM SurfaceStepResult

/-- The syntax needed to emit a checked typed result. -/
structure SurfaceMaterialization where
  /-- Surface result corresponding to the checked typed result. -/
  surface : SurfaceStepResult
  /-- Section variables used while validating the typed result. -/
  sectionFVars : Array Expr

end PTran.Reformulation.Internal
