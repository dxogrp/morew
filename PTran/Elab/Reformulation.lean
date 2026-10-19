import PTran.Transform
import Lean.Meta.Basic

/-!
# Typed reformulation runner support

This module contains the data model shared by reformulation step elaborators.
It deliberately does not know about the surface command: steps describe typed
semantic and presentation changes, while the command runner is responsible for
validating and committing them.
-/

namespace PTran.Elab.Reformulation

open Lean Lean.Meta

/-! ## Visible names -/

/-- The user-visible part of a name.  Macro scopes are irrelevant for name
allocation, but ordinary namespace components are retained. -/
def visibleName (name : Name) : Name :=
  name.eraseMacroScopes

/-- Whether two names have the same user-visible spelling. -/
def sameVisibleName (left right : Name) : Bool :=
  visibleName left == visibleName right

/-- Presentation names live in independent namespaces.  In particular, a
decision binder and a constraint label may have the same visible spelling. -/
inductive NameNamespace where
  | decisionBinder
  | constraintLabel
  deriving Inhabited, BEq, Repr

/-- The source and allocation policy of a requested presentation name. -/
inductive NameRequestKind where
  | explicitDecisionBinder
  | inferredDecisionBinder
  | explicitConstraintLabel
  | fixedPublicDefault
  | generatedBinderFamily
  | generatedRowFamily
  deriving Inhabited, BEq, Repr

/-- The namespace selected by a name-request category. -/
def NameRequestKind.namespace : NameRequestKind → NameNamespace
  | .explicitDecisionBinder | .inferredDecisionBinder | .generatedBinderFamily =>
      .decisionBinder
  | .explicitConstraintLabel | .fixedPublicDefault | .generatedRowFamily =>
      .constraintLabel

/-- Exact requests are rejected on collision; generated requests are the only
requests which may receive a deterministic numeric suffix. -/
def NameRequestKind.isGenerated : NameRequestKind → Bool
  | .generatedBinderFamily | .generatedRowFamily => true
  | _ => false

/-- One atomic presentation-name request.  `id` is an internal key used by the
step materializer; it need only be unique within the request batch. -/
structure NameRequest where
  /-- Key used to recover this request's allocation. -/
  id : Nat
  /-- Allocation policy and presentation namespace. -/
  kind : NameRequestKind
  /-- Preferred user-visible name. -/
  requested : Name
  /-- Syntax used to locate allocation diagnostics. -/
  ref : Syntax := Syntax.missing

/-- The namespace in which a request is allocated. -/
def NameRequest.namespace (request : NameRequest) : NameNamespace :=
  request.kind.namespace

/-- Names active at the beginning of a step.  Keeping the two arrays separate
is what permits a binder and a constraint label to share a spelling. -/
structure NameInventory where
  /-- Occupied decision-binder names. -/
  decisionBinders : Array Name := #[]
  /-- Occupied constraint-label names. -/
  constraintLabels : Array Name := #[]

/-- Test whether a visible name is occupied in one presentation namespace. -/
def NameInventory.contains (inventory : NameInventory)
    (ns : NameNamespace) (name : Name) : Bool :=
  let names := match ns with
    | .decisionBinder => inventory.decisionBinders
    | .constraintLabel => inventory.constraintLabels
  names.any fun occupied => sameVisibleName occupied name

/-- Add a name to one presentation namespace. -/
def NameInventory.insert (inventory : NameInventory)
    (ns : NameNamespace) (name : Name) : NameInventory :=
  if inventory.contains ns name then
    inventory
  else
    let name := visibleName name
    match ns with
    | .decisionBinder => { inventory with
        decisionBinders := inventory.decisionBinders.push name }
    | .constraintLabel => { inventory with
        constraintLabels := inventory.constraintLabels.push name }

/-- The result of allocating one request. -/
structure NameAssignment where
  /-- Key of the request receiving this assignment. -/
  requestId : Nat
  /-- Allocated user-visible name. -/
  name : Name
  deriving Inhabited, BEq, Repr

/-- An allocation is ordered like the input request batch. -/
abbrev NameAllocation := Array NameAssignment

/-- Look up the name allocated for an internal request key. -/
def NameAllocation.findName? (allocation : NameAllocation)
    (requestId : Nat) : Option Name :=
  (allocation.find? fun assignment => assignment.requestId == requestId).map (·.name)

/-- A failure detected before any part of a name batch is committed. -/
inductive NamePreflightError where
  | duplicateRequestId (request : NameRequest)
  | collision (request : NameRequest) (occupied : Name)

/-- The source location associated with a name preflight failure. -/
def NamePreflightError.ref : NamePreflightError → Syntax
  | .duplicateRequestId request | .collision request _ => request.ref

/-- A concise diagnostic for a name preflight failure. -/
def NamePreflightError.message : NamePreflightError → MessageData
  | .duplicateRequestId request =>
      m!"duplicate internal name-request id `{request.id}`"
  | .collision request occupied =>
      match request.kind with
      | .fixedPublicDefault =>
          m!"default constraint label `{visibleName occupied}` is already in use; choose an explicit label with `as`"
      | .explicitDecisionBinder | .inferredDecisionBinder =>
          m!"decision variable `{visibleName occupied}` already exists"
      | .explicitConstraintLabel =>
          m!"constraint label `{visibleName occupied}` already exists"
      | .generatedBinderFamily | .generatedRowFamily =>
          m!"internal error: generated name `{visibleName occupied}` was not freshened"

/-- Candidate zero is the stem itself; later candidates use `_1`, `_2`, and
so on while preserving the stem's qualified prefix. -/
def generatedCandidate (stem : Name) (index : Nat) : Name :=
  let stem := visibleName stem
  if index == 0 then stem else stem.appendIndexAfter index

private partial def firstAvailableGeneratedName (inventory : NameInventory)
    (ns : NameNamespace) (stem : Name) (index : Nat := 0) : Name :=
  let candidate := generatedCandidate stem index
  if inventory.contains ns candidate then
    firstAvailableGeneratedName inventory ns stem (index + 1)
  else
    candidate

/-- Preflight and allocate a complete name batch without changing the supplied
inventory.  Exact and fixed-default requests are reserved first, so generated
families cannot steal a later exact request.  Generated requests are then
freshened in source order. -/
def preflightNameRequests (active : NameInventory)
    (requests : Array NameRequest) : Except NamePreflightError NameAllocation := do
  let mut requestIds : Array Nat := #[]
  for request in requests do
    if requestIds.contains request.id then
      throw (.duplicateRequestId request)
    requestIds := requestIds.push request.id

  let mut reserved := active
  let mut allocated : Array NameAssignment := #[]
  for request in requests do
    unless request.kind.isGenerated do
      if reserved.contains request.namespace request.requested then
        throw (.collision request request.requested)
      reserved := reserved.insert request.namespace request.requested
      allocated := allocated.push {
        requestId := request.id
        name := request.requested
      }

  for request in requests do
    if request.kind.isGenerated then
      let name := firstAvailableGeneratedName reserved request.namespace request.requested
      reserved := reserved.insert request.namespace name
      allocated := allocated.push { requestId := request.id, name }

  let mut result := #[]
  for request in requests do
    let some assignment := allocated.find? fun candidate =>
        candidate.requestId == request.id
      | unreachable!
    result := result.push assignment
  pure result

/-! ## Typed presentation state -/

/-- One typed decision-binder presentation entry. -/
structure BinderEntry where
  /-- User-visible binder name. -/
  name : Name
  /-- Elaborated type of the binder component. -/
  type : Expr
  /-- Source syntax associated with the binder. -/
  ref : Syntax := Syntax.missing
  deriving Inhabited

/-- One typed, named constraint.  `predicate` is the closed function from the
current decision domain to `Prop`, not reparsable source syntax. -/
structure ConstraintEntry where
  /-- User-visible constraint label. -/
  name : Name
  /-- Closed predicate on the current decision domain. -/
  predicate : Expr
  /-- Source syntax associated with the constraint. -/
  ref : Syntax := Syntax.missing
  deriving Inhabited

/-- The typed presentation corresponding to a canonical semantic problem. -/
structure PresentationState where
  /-- Optimization sense displayed by the presentation. -/
  sense : PTran.Syntax.ObjectiveSense
  /-- Type of the presented decision domain. -/
  domainType : Expr
  /-- Type of objective values. -/
  valueType : Expr
  /-- Ordered decision-binder entries. -/
  binders : Array BinderEntry
  /-- Objective function on `domainType`. -/
  objective : Expr
  /-- Ordered named feasibility predicates. -/
  constraints : Array ConstraintEntry := #[]

private def rightAssociatedConjunction : List Expr → Expr
  | [] => mkConst ``True
  | [proposition] => proposition
  | proposition :: rest =>
      mkApp2 (mkConst ``And) proposition (rightAssociatedConjunction rest)

private def ensureIsType (type : Expr) (description : String) : MetaM Unit := do
  let sort ← whnf (← inferType type)
  unless sort.isSort do
    throwError "{description} is not a type"

private def leftAssociatedDomain (binders : Array BinderEntry) : MetaM Expr := do
  let some first := binders[0]?
    | throwError "a problem presentation requires at least one decision variable"
  let mut domain := first.type
  for index in [1:binders.size] do
    domain ← mkAppM ``Prod #[domain, binders[index]!.type]
  pure domain

/-- Construct the canonical semantic problem represented by a presentation.
The feasibility predicate is deliberately normalized to `True`, a singleton,
or a right-associated conjunction. -/
def PresentationState.canonicalProblem (state : PresentationState) : MetaM Expr := do
  ensureIsType state.domainType "presentation decision domain"
  ensureIsType state.valueType "presentation objective-value type"
  for binder in state.binders do
    ensureIsType binder.type s!"decision binder `{binder.name}` type"
  let representedDomain ← leftAssociatedDomain state.binders
  unless ← isDefEq representedDomain state.domainType do
    throwError "presentation binder product does not match its decision domain"
  let objectiveType ← inferType state.objective
  let expectedObjectiveType ← mkArrow state.domainType state.valueType
  unless ← isDefEq objectiveType expectedObjectiveType do
    throwError "presentation objective has type{indentExpr objectiveType}\nbut expected{indentExpr expectedObjectiveType}"
  let expectedPredicateType ← mkArrow state.domainType (mkSort Level.zero)
  for constraint in state.constraints do
    let predicateType ← inferType constraint.predicate
    unless ← isDefEq predicateType expectedPredicateType do
      throwError "constraint `{constraint.name}` has predicate type{indentExpr predicateType}\nbut expected{indentExpr expectedPredicateType}"
  let feasible ← withLocalDeclD `point state.domainType fun point => do
    let propositions := state.constraints.map fun constraint =>
      mkApp constraint.predicate point
    mkLambdaFVars #[point] <| rightAssociatedConjunction propositions.toList
  mkAppM ``PTran.Problem.mk #[state.objective, feasible]

/-- Build the active-name inventory for a typed presentation. -/
def PresentationState.nameInventory (state : PresentationState) : NameInventory :=
  let decisionBinders := state.binders.foldl
    (fun inventory binder => inventory.insert .decisionBinder binder.name) {}
  state.constraints.foldl
    (fun inventory constraint => inventory.insert .constraintLabel constraint.name)
    decisionBinders

/-- Replace one binder in place.  The equality is checked by the runner before
the edit is committed and explains how the old and new component types agree. -/
structure BinderReplacement where
  /-- Position of the binder replaced in place. -/
  index : Nat
  /-- Replacement binder entry. -/
  entry : BinderEntry
  /-- Evidence that the component type is preserved. -/
  typeEquality : Expr

/-- Append one binder.  `domainEquality` relates the semantic next domain to
the product domain represented by the resulting binder list. -/
structure BinderAddition where
  /-- Binder appended to the presentation. -/
  entry : BinderEntry
  /-- Evidence relating the resulting product domain to the semantic domain. -/
  domainEquality : Expr

/-- Replace the objective by a typed function on the next decision domain. -/
structure ObjectiveReplacement where
  /-- Replacement objective function. -/
  objective : Expr
  /-- Pointwise equality between the semantic and presented objectives. -/
  pointwiseEquality : Expr

/-- Replace one original constraint in place by zero, one, or several ordered
constraints.  An empty `entries` array is a proof-producing removal. -/
structure ConstraintReplacement where
  /-- Position of the original constraint. -/
  index : Nat
  /-- Ordered constraints spliced into the original position. -/
  entries : Array ConstraintEntry
  /-- Pointwise feasibility equivalence supporting the edit. -/
  pointwiseIff : Expr

/-- Append one constraint after all in-place replacements. -/
structure ConstraintAddition where
  /-- Constraint appended to the presentation. -/
  entry : ConstraintEntry
  /-- Pointwise feasibility equivalence supporting the addition. -/
  pointwiseIff : Expr

/-- An atomic, ordered change to typed presentation state.  Replacement indices
refer to the state at step entry, never to a partially edited array. -/
structure PresentationDelta where
  /-- Optional replacement decision-domain type. -/
  domainType? : Option Expr := none
  /-- Optional replacement objective-value type. -/
  valueType? : Option Expr := none
  /-- Ordered in-place binder replacements. -/
  binderReplacements : Array BinderReplacement := #[]
  /-- Ordered binders appended after replacements. -/
  binderAdditions : Array BinderAddition := #[]
  /-- Optional objective replacement. -/
  objective? : Option ObjectiveReplacement := none
  /-- Constraint replacements indexed in the entry presentation. -/
  constraintReplacements : Array ConstraintReplacement := #[]
  /-- Constraints appended after all replacements. -/
  constraintAdditions : Array ConstraintAddition := #[]
  /-- Pointwise equality from the next semantic objective to the canonical
  objective after applying this delta.  Required when committing a step. -/
  normalizationObjectiveEquality? : Option Expr := none
  /-- Pointwise iff from the next semantic feasibility predicate to canonical
  feasibility after applying this delta.  Required when committing a step. -/
  normalizationFeasibleIff? : Option Expr := none

/-- A structural presentation edit failed validation. -/
inductive PresentationError where
  | emptyBinderList
  | binderIndexOutOfBounds (index size : Nat)
  | duplicateBinderReplacement (index : Nat)
  | constraintIndexOutOfBounds (index size : Nat)
  | duplicateConstraintReplacement (index : Nat)
  deriving Inhabited, BEq, Repr

private def validateBinderReplacements (state : PresentationState)
    (delta : PresentationDelta) : Except PresentationError Unit := do
  let mut seen : Array Nat := #[]
  for replacement in delta.binderReplacements do
    if replacement.index >= state.binders.size then
      throw (.binderIndexOutOfBounds replacement.index state.binders.size)
    if seen.contains replacement.index then
      throw (.duplicateBinderReplacement replacement.index)
    seen := seen.push replacement.index

private def validateConstraintReplacements (state : PresentationState)
    (delta : PresentationDelta) : Except PresentationError Unit := do
  let mut seen : Array Nat := #[]
  for replacement in delta.constraintReplacements do
    if replacement.index >= state.constraints.size then
      throw (.constraintIndexOutOfBounds replacement.index state.constraints.size)
    if seen.contains replacement.index then
      throw (.duplicateConstraintReplacement replacement.index)
    seen := seen.push replacement.index

/-- Apply a validated presentation delta atomically.  Constraint replacements
are spliced at their original locations, which preserves order for zero, one,
and many replacement entries. -/
def PresentationState.applyDelta (state : PresentationState)
    (delta : PresentationDelta) : Except PresentationError PresentationState := do
  validateBinderReplacements state delta
  validateConstraintReplacements state delta

  let mut binders := #[]
  for index in [:state.binders.size] do
    match delta.binderReplacements.find? fun replacement => replacement.index == index with
    | some replacement => binders := binders.push replacement.entry
    | none => binders := binders.push state.binders[index]!
  for addition in delta.binderAdditions do
    binders := binders.push addition.entry
  if binders.isEmpty then
    throw .emptyBinderList

  let mut constraints := #[]
  for index in [:state.constraints.size] do
    match delta.constraintReplacements.find? fun replacement => replacement.index == index with
    | some replacement => constraints := constraints ++ replacement.entries
    | none => constraints := constraints.push state.constraints[index]!
  for addition in delta.constraintAdditions do
    constraints := constraints.push addition.entry

  pure {
    sense := state.sense
    domainType := delta.domainType?.getD state.domainType
    valueType := delta.valueType?.getD state.valueType
    binders
    objective := delta.objective?.map (·.objective) |>.getD state.objective
    constraints
  }

/-! ## Compositional step and certificate interfaces -/

/-- One exact global declaration name requested by the command or a terminal
step.  Global declaration names are never freshened. -/
structure DeclarationNameRequest where
  /-- Exact global declaration name requested. -/
  name : Name
  /-- Syntax used to locate collision diagnostics. -/
  ref : Syntax := Syntax.missing

/-- A complete declaration-name batch failed before emission began. -/
inductive DeclarationPreflightError where
  | duplicate (request : DeclarationNameRequest)
  | alreadyDeclared (request : DeclarationNameRequest)

/-- Preflight exact global names against both the current environment and the
rest of the batch. -/
def preflightDeclarationNames (env : Environment)
    (requests : Array DeclarationNameRequest) :
    Except DeclarationPreflightError Unit := do
  let mut reserved : Array Name := #[]
  for request in requests do
    let visible := visibleName request.name
    if reserved.any fun name => name == visible then
      throw (.duplicate request)
    if env.contains visible then
      throw (.alreadyDeclared request)
    reserved := reserved.push visible

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

private def BinderEntry.replaceFVars (entry : BinderEntry)
    (oldFVars newFVars : Array Expr) : BinderEntry :=
  { entry with type := entry.type.replaceFVars oldFVars newFVars }

private def ConstraintEntry.replaceFVars (entry : ConstraintEntry)
    (oldFVars newFVars : Array Expr) : ConstraintEntry :=
  { entry with predicate := entry.predicate.replaceFVars oldFVars newFVars }

/-- Rebase all expressions in a presentation onto a new set of section free
variables created by `runTermElabM`. -/
def PresentationState.replaceFVars (state : PresentationState)
    (oldFVars newFVars : Array Expr) : PresentationState := {
  state with
  domainType := state.domainType.replaceFVars oldFVars newFVars
  valueType := state.valueType.replaceFVars oldFVars newFVars
  binders := state.binders.map (·.replaceFVars oldFVars newFVars)
  objective := state.objective.replaceFVars oldFVars newFVars
  constraints := state.constraints.map (·.replaceFVars oldFVars newFVars)
}

/-- Rebase all proof and type expressions in a presentation delta. -/
def PresentationDelta.replaceFVars (delta : PresentationDelta)
    (oldFVars newFVars : Array Expr) : PresentationDelta := {
  domainType? := delta.domainType?.map (·.replaceFVars oldFVars newFVars)
  valueType? := delta.valueType?.map (·.replaceFVars oldFVars newFVars)
  binderReplacements := delta.binderReplacements.map fun replacement => {
    replacement with
    entry := replacement.entry.replaceFVars oldFVars newFVars
    typeEquality := replacement.typeEquality.replaceFVars oldFVars newFVars
  }
  binderAdditions := delta.binderAdditions.map fun addition => {
    addition with
    entry := addition.entry.replaceFVars oldFVars newFVars
    domainEquality := addition.domainEquality.replaceFVars oldFVars newFVars
  }
  objective? := delta.objective?.map fun replacement => {
    objective := replacement.objective.replaceFVars oldFVars newFVars
    pointwiseEquality := replacement.pointwiseEquality.replaceFVars oldFVars newFVars
  }
  constraintReplacements := delta.constraintReplacements.map fun replacement => {
    replacement with
    entries := replacement.entries.map (·.replaceFVars oldFVars newFVars)
    pointwiseIff := replacement.pointwiseIff.replaceFVars oldFVars newFVars
  }
  constraintAdditions := delta.constraintAdditions.map fun addition => {
    entry := addition.entry.replaceFVars oldFVars newFVars
    pointwiseIff := addition.pointwiseIff.replaceFVars oldFVars newFVars
  }
  normalizationObjectiveEquality? :=
    delta.normalizationObjectiveEquality?.map (·.replaceFVars oldFVars newFVars)
  normalizationFeasibleIff? :=
    delta.normalizationFeasibleIff?.map (·.replaceFVars oldFVars newFVars)
}

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
