import PTran.Elab.Reformulation.Presentation
import PTran.Transform

/-!
# Typed reformulation runner

Typed step interfaces, certificate composition, normalization, and atomic commit.
This module does not depend on the surface reformulation command.
-/

namespace PTran.Elab.Reformulation

open Lean Lean.Meta

/-! ## Compositional step and certificate interfaces -/

/-- A declaration requested by a terminal step.  Declaration-name preflight
and actual environment mutation remain responsibilities of the command runner. -/
structure CompanionRequest where
  /-- Exact global name of the companion declaration. -/
  name : Name
  /-- Elaborated type of the companion declaration. -/
  type : Expr
  /-- Elaborated value of the companion declaration. -/
  value : Expr
  /-- Syntax used to locate companion diagnostics. -/
  ref : Syntax := Syntax.missing

/-- The exact global-name request corresponding to a companion declaration. -/
def CompanionRequest.nameRequest (request : CompanionRequest) :
    DeclarationNameRequest := {
  name := request.name
  ref := request.ref
}

/-- Whether another reformulation step may follow the current result. -/
inductive StepStatus where
  | continue
  | terminal
  deriving Inhabited, BEq, Repr

/-- The typed, uncommitted result produced by one primitive step. -/
structure StepResult where
  /-- Natural semantic problem produced by the primitive step. -/
  nextSemantic : Expr
  /-- Certificate from the current semantic problem to `nextSemantic`. -/
  primitiveCertificate : Expr
  /-- Ordered edits defining the next canonical presentation. -/
  presentationDelta : PresentationDelta
  /-- Whether further steps may follow this result. -/
  status : StepStatus := .continue
  /-- Additional global declarations requested by the step. -/
  companions : Array CompanionRequest := #[]

/-- Checked pointwise normalization from the natural semantic result of a
step to the canonical problem represented by its presentation. -/
structure PointwiseNormalization where
  /-- Natural semantic problem being normalized. -/
  semantic : Expr
  /-- Canonical presentation problem obtained by normalization. -/
  canonical : Expr
  /-- Pointwise equality of semantic and canonical objectives. -/
  objectiveEquality : Expr
  /-- Pointwise equivalence of semantic and canonical feasibility. -/
  feasibleIff : Expr
  /-- Global-equivalence certificate induced by the pointwise proofs. -/
  equivalence : Expr

/-- The first phase of a step.  A handler exposes its entire name batch before
its materializer is allowed to construct the typed result. -/
structure StepPlan (m : Type → Type) where
  /-- Complete presentation-name batch required by the step. -/
  nameRequests : Array NameRequest
  /-- Construct the typed result from the allocated names. -/
  materialize : NameAllocation → m StepResult

/-- Preflight the complete request batch before allowing a step to materialize
typed expressions or presentation edits. -/
def StepPlan.run [Monad m] (plan : StepPlan m) (active : NameInventory) :
    ExceptT NamePreflightError m StepResult := do
  let allocation ← ExceptT.mk <| pure <|
    preflightNameRequests active plan.nameRequests
  plan.materialize allocation

/-- Typed state threaded by the command runner. -/
structure RunnerState where
  /-- Current natural semantic problem. -/
  semantic : Expr
  /-- Current canonical presentation problem. -/
  canonical : Expr
  /-- Domain type of `semantic`. -/
  semanticDomainType : Expr
  /-- Objective-value type of `semantic`. -/
  semanticValueType : Expr
  /-- Typed presentation corresponding to `canonical`. -/
  presentation : PresentationState
  /-- Composed certificate ending at `semantic`. -/
  accumulatedCertificate : Expr
  /-- Checked normalization from `semantic` to `canonical`. -/
  normalization : PointwiseNormalization
  /-- Companion declarations accumulated from committed steps. -/
  companions : Array CompanionRequest := #[]
  /-- Whether the runner accepts another step. -/
  status : StepStatus := .continue

/-- Rebase a companion declaration onto a new section-variable context. -/
def CompanionRequest.replaceFVars (request : CompanionRequest)
    (oldFVars newFVars : Array Expr) : CompanionRequest := {
  request with
  type := request.type.replaceFVars oldFVars newFVars
  value := request.value.replaceFVars oldFVars newFVars
}

/-- Rebase a typed step result onto a new section-variable context. -/
def StepResult.replaceFVars (result : StepResult)
    (oldFVars newFVars : Array Expr) : StepResult := {
  result with
  nextSemantic := result.nextSemantic.replaceFVars oldFVars newFVars
  primitiveCertificate := result.primitiveCertificate.replaceFVars oldFVars newFVars
  presentationDelta := result.presentationDelta.replaceFVars oldFVars newFVars
  companions := result.companions.map (·.replaceFVars oldFVars newFVars)
}

/-- Rebase a pointwise normalization onto a new section-variable context. -/
def PointwiseNormalization.replaceFVars (normalization : PointwiseNormalization)
    (oldFVars newFVars : Array Expr) : PointwiseNormalization := {
  semantic := normalization.semantic.replaceFVars oldFVars newFVars
  canonical := normalization.canonical.replaceFVars oldFVars newFVars
  objectiveEquality := normalization.objectiveEquality.replaceFVars oldFVars newFVars
  feasibleIff := normalization.feasibleIff.replaceFVars oldFVars newFVars
  equivalence := normalization.equivalence.replaceFVars oldFVars newFVars
}

/-- Rebase every typed expression retained by the runner onto the section
variables supplied by a later `runTermElabM` invocation. -/
def RunnerState.replaceFVars (state : RunnerState)
    (oldFVars newFVars : Array Expr) : RunnerState := {
  semantic := state.semantic.replaceFVars oldFVars newFVars
  canonical := state.canonical.replaceFVars oldFVars newFVars
  semanticDomainType := state.semanticDomainType.replaceFVars oldFVars newFVars
  semanticValueType := state.semanticValueType.replaceFVars oldFVars newFVars
  presentation := state.presentation.replaceFVars oldFVars newFVars
  accumulatedCertificate := state.accumulatedCertificate.replaceFVars oldFVars newFVars
  normalization := state.normalization.replaceFVars oldFVars newFVars
  companions := state.companions.map (·.replaceFVars oldFVars newFVars)
  status := state.status
}

/-- The algebraic operations for a certificate relation.  Keeping declaration
names as data leaves the runner open to relations other than equivalence. -/
structure CertificateRunner where
  /-- Declaration implementing the certificate relation. -/
  relation : Name
  /-- Declaration implementing reflexivity for the relation. -/
  refl : Name
  /-- Declaration implementing transitivity for the relation. -/
  trans : Name
  /-- Optional declaration lifting global equivalence into the relation. -/
  liftEquivalence? : Option Name := none

/-- Form the type `relation source target` selected by a certificate runner. -/
def CertificateRunner.relationType (runner : CertificateRunner)
    (source target : Expr) : MetaM Expr :=
  mkAppM runner.relation #[source, target]

/-- Construct a reflexive certificate for one semantic problem. -/
def CertificateRunner.reflexivity (runner : CertificateRunner)
    (optimizationProblem : Expr) : MetaM Expr :=
  mkAppM runner.refl #[optimizationProblem]

/-- Compose two certificates in the selected relation. -/
def CertificateRunner.compose (runner : CertificateRunner)
    (left right : Expr) : MetaM Expr :=
  mkAppM runner.trans #[left, right]

/-- Lift a primitive global-equivalence certificate into the selected relation
when the relation requires an explicit conversion. -/
def CertificateRunner.liftEquivalence (runner : CertificateRunner)
    (certificate : Expr) : MetaM Expr :=
  match runner.liftEquivalence? with
  | none => pure certificate
  | some lift => mkAppM lift #[certificate]

/-- The exact relation used by the current public reformulation command. -/
def globalEquivalenceRunner : CertificateRunner where
  relation := ``PTran.GlobalEquivalence
  refl := ``PTran.GlobalEquivalence.refl
  trans := ``PTran.GlobalEquivalence.trans

private def problemTypeParts (optimizationProblem : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType optimizationProblem)
  unless type.getAppFn.isConstOf ``PTran.Problem && type.getAppNumArgs == 2 do
    throwError "expected an expression of type `PTran.Problem _ _`"
  pure (type.getAppArgs[0]!, type.getAppArgs[1]!)

private def ensureHasType (value expected : Expr) (description : String) : MetaM Unit := do
  let actual ← inferType value
  unless ← isDefEq actual expected do
    throwError "{description} has type{indentExpr actual}\nbut expected{indentExpr expected}"

/-- Validate the semantic, pointwise, and global-equivalence parts of a
normalization witness. -/
def PointwiseNormalization.check (normalization : PointwiseNormalization) :
    MetaM Unit := do
  let (semanticDomain, semanticValue) ← problemTypeParts normalization.semantic
  let (canonicalDomain, canonicalValue) ← problemTypeParts normalization.canonical
  unless ← isDefEq semanticDomain canonicalDomain do
    throwError "normalization changed the decision-domain type"
  unless ← isDefEq semanticValue canonicalValue do
    throwError "normalization changed the objective value type"
  let semanticObjective ← mkAppM ``PTran.Problem.objective #[normalization.semantic]
  let canonicalObjective ← mkAppM ``PTran.Problem.objective #[normalization.canonical]
  let semanticFeasible ← mkAppM ``PTran.Problem.feasible #[normalization.semantic]
  let canonicalFeasible ← mkAppM ``PTran.Problem.feasible #[normalization.canonical]
  let objectiveType ← withLocalDeclD `point semanticDomain fun point => do
    let equality ← mkEq (mkApp semanticObjective point)
      (mkApp canonicalObjective point)
    mkForallFVars #[point] equality
  let feasibleType ← withLocalDeclD `point semanticDomain fun point => do
    mkForallFVars #[point] <| mkApp2 (mkConst ``Iff)
      (mkApp semanticFeasible point) (mkApp canonicalFeasible point)
  ensureHasType normalization.objectiveEquality objectiveType
    "normalization objective proof"
  ensureHasType normalization.feasibleIff feasibleType
    "normalization feasibility proof"
  let expectedEquivalence ← mkAppM ``PTran.GlobalEquivalence
    #[normalization.semantic, normalization.canonical]
  ensureHasType normalization.equivalence expectedEquivalence
    "normalization equivalence certificate"

private def validateDeltaEvidence (state : RunnerState) (result : StepResult)
    (normalization : PointwiseNormalization) (presentation : PresentationState)
    (semanticDomain : Expr) : MetaM Unit := do
  for replacement in result.presentationDelta.binderReplacements do
    let previous := state.presentation.binders[replacement.index]!
    let expected ← mkEq previous.type replacement.entry.type
    ensureHasType replacement.typeEquality expected
      s!"decision-binder replacement `{replacement.entry.name}` type equality"
  for addition in result.presentationDelta.binderAdditions do
    let expected ← mkEq semanticDomain presentation.domainType
    ensureHasType addition.domainEquality expected
      s!"decision-binder addition `{addition.entry.name}` domain equality"
  if let some replacement := result.presentationDelta.objective? then
    let expected ← inferType normalization.objectiveEquality
    ensureHasType replacement.pointwiseEquality expected
      "objective replacement pointwise equality"
  let feasibilityEvidenceType ← inferType normalization.feasibleIff
  for replacement in result.presentationDelta.constraintReplacements do
    ensureHasType replacement.pointwiseIff feasibilityEvidenceType
      s!"constraint replacement at index {replacement.index} feasibility equivalence"
  for addition in result.presentationDelta.constraintAdditions do
    ensureHasType addition.pointwiseIff feasibilityEvidenceType
      s!"constraint addition `{addition.entry.name}` feasibility equivalence"

/-- Validate and atomically commit a typed primitive step.  Presentation
errors are returned without changing the caller's state; proof/type failures
remain ordinary elaboration errors. -/
def RunnerState.commit (state : RunnerState) (runner : CertificateRunner)
    (result : StepResult) :
    MetaM (Except PresentationError RunnerState) := do
  if state.status == .terminal then
    throwError "cannot commit a reformulation step after a terminal result"
  let (currentDomain, currentValue) ← problemTypeParts state.semantic
  unless ← isDefEq currentDomain state.semanticDomainType do
    throwError "runner state records the wrong semantic decision-domain type"
  unless ← isDefEq currentValue state.semanticValueType do
    throwError "runner state records the wrong semantic objective-value type"
  let currentCanonical ← state.presentation.canonicalProblem
  unless ← isDefEq currentCanonical state.canonical do
    throwError "runner canonical problem does not match its presentation"
  let expectedPrimitive ← runner.relationType state.semantic result.nextSemantic
  ensureHasType result.primitiveCertificate expectedPrimitive
    "primitive reformulation certificate"
  for companion in result.companions do
    let typeType ← whnf (← inferType companion.type)
    unless typeType.isSort do
      throwError "companion declaration `{companion.name}` has a non-type declaration type"
    ensureHasType companion.value companion.type
      s!"companion declaration `{companion.name}` value"
  let presentation ← match state.presentation.applyDelta result.presentationDelta with
    | .ok presentation => pure presentation
    | .error error => return .error error
  let expectedCanonical ← presentation.canonicalProblem
  let some objectiveEquality :=
      result.presentationDelta.normalizationObjectiveEquality?
    | throwError "presentation delta is missing semantic objective normalization evidence"
  let some feasibleIff := result.presentationDelta.normalizationFeasibleIff?
    | throwError "presentation delta is missing semantic feasibility normalization evidence"
  let equivalence ← mkAppM ``PTran.pointwiseEquivalence
    #[result.nextSemantic, expectedCanonical, objectiveEquality, feasibleIff]
  let normalization : PointwiseNormalization := {
    semantic := result.nextSemantic
    canonical := expectedCanonical
    objectiveEquality
    feasibleIff
    equivalence
  }
  normalization.check
  let (semanticDomainType, semanticValueType) ← problemTypeParts result.nextSemantic
  unless ← isDefEq semanticDomainType presentation.domainType do
    throwError "updated presentation has the wrong decision-domain type"
  unless ← isDefEq semanticValueType presentation.valueType do
    throwError "updated presentation has the wrong objective-value type"
  validateDeltaEvidence state result normalization presentation semanticDomainType
  let accumulatedCertificate ←
    runner.compose state.accumulatedCertificate result.primitiveCertificate
  pure <| .ok {
    semantic := result.nextSemantic
    canonical := normalization.canonical
    semanticDomainType
    semanticValueType
    presentation
    accumulatedCertificate
    normalization
    companions := state.companions ++ result.companions
    status := result.status
  }

/-- Compose the raw semantic chain with its final canonical normalization. -/
def RunnerState.finalCertificate (state : RunnerState)
    (runner : CertificateRunner) : MetaM Expr := do
  let normalization ← runner.liftEquivalence state.normalization.equivalence
  runner.compose state.accumulatedCertificate normalization


end PTran.Elab.Reformulation
