import PTran.Elab.Reformulation
import Mathlib.Data.Nat.Basic

/-!
# Tests for the typed reformulation runner model

These tests exercise the pure, reusable pieces of the runner independently of
the reformulation command's surface syntax.
-/

namespace PTranTest.RunnerInternals

open Lean
open PTran.Elab.Reformulation

private def expect (condition : Bool) (message : String) :
    Lean.Elab.Command.CommandElabM Unit :=
  unless condition do
    throwError message

/-! ## Visible names and allocation policy -/

run_cmd do
  let hygienic := Lean.addMacroScope `PTranTest `Model.x 17
  expect (sameVisibleName hygienic `Model.x)
    "macro scopes changed the visible spelling of a name"
  expect (!sameVisibleName hygienic `Other.x)
    "visible-name comparison discarded an ordinary namespace component"

run_cmd do
  let active : NameInventory := {
    decisionBinders := #[`shared]
  }
  let request : NameRequest := {
    id := 0
    kind := .explicitConstraintLabel
    requested := `shared
  }
  match preflightNameRequests active #[request] with
  | .ok allocation =>
      expect (allocation.findName? 0 == some `shared)
        "binder and constraint namespaces were not allocated independently"
  | .error _ =>
      throwError "a binder incorrectly occupied the constraint-label namespace"

run_cmd do
  let active : NameInventory := {
    decisionBinders := #[`takenBinder]
    constraintLabels := #[`takenLabel]
  }
  let explicit : NameRequest := {
    id := 0
    kind := .explicitDecisionBinder
    requested := `takenBinder
  }
  match preflightNameRequests active #[explicit] with
  | .error (.collision request _) =>
      expect (request.id == explicit.id)
        "explicit-name collision was reported for the wrong request"
  | _ => throwError "an explicit name was freshened instead of rejected"

  let fixed : NameRequest := {
    id := 1
    kind := .fixedPublicDefault
    requested := `takenLabel
  }
  match preflightNameRequests active #[fixed] with
  | .error (.collision request _) =>
      expect (request.id == fixed.id)
        "fixed-default collision was reported for the wrong request"
  | _ => throwError "a fixed public default was freshened instead of rejected"

private def generatedRequests : Array NameRequest := #[
  { id := 0, kind := .generatedBinderFamily, requested := `stem },
  { id := 1, kind := .generatedBinderFamily, requested := `stem },
  { id := 2, kind := .generatedBinderFamily, requested := `stem }
]

private def expectedGenerated : Array NameAssignment := #[
  { requestId := 0, name := `stem },
  { requestId := 1, name := `stem_1 },
  { requestId := 2, name := `stem_2 }
]

run_cmd do
  let forward : NameInventory := {
    decisionBinders := #[`unrelatedA, `unrelatedB]
  }
  let reverse : NameInventory := {
    decisionBinders := #[`unrelatedB, `unrelatedA]
  }
  let .ok forwardAllocation := preflightNameRequests forward generatedRequests
    | throwError "generated-name allocation unexpectedly failed"
  let .ok reverseAllocation := preflightNameRequests reverse generatedRequests
    | throwError "generated-name allocation unexpectedly depended on inventory order"
  expect (forwardAllocation == expectedGenerated)
    "generated names were not allocated as stem, stem_1, stem_2"
  expect (reverseAllocation == expectedGenerated)
    "reversing inventory insertion order changed generated allocation"

run_cmd do
  let requests : Array NameRequest := #[
    { id := 0, kind := .generatedBinderFamily, requested := `reserved },
    { id := 1, kind := .explicitDecisionBinder, requested := `reserved }
  ]
  let .ok allocation := preflightNameRequests {} requests
    | throwError "a valid mixed exact/generated batch was rejected"
  expect (allocation.findName? 0 == some `reserved_1)
    "a generated request stole a name from a later exact request"
  expect (allocation.findName? 1 == some `reserved)
    "a later exact request did not retain its requested name"

run_cmd do
  expect (generatedCandidate `Rows.slack 2 == `Rows.slack_2)
    "generated freshening did not preserve a qualified prefix"

  let reuse : NameRequest := {
    id := 0
    kind := .explicitConstraintLabel
    requested := `positive
  }
  match preflightNameRequests { constraintLabels := #[`positive] } #[reuse] with
  | .error (.collision _ _) => pure ()
  | _ => throwError "a name scheduled for same-step removal was reused"
  match preflightNameRequests {} #[reuse] with
  | .ok allocation =>
      expect (allocation.findName? 0 == some `positive)
        "a name removed by a completed previous step was not reusable"
  | .error _ => throwError "a previously removed name remained reserved"

/-! ## Atomic presentation deltas -/

private def placeholder : Expr := .const ``True.intro []

private def constraint (name : Name) : ConstraintEntry := {
  name
  predicate := placeholder
}

private def basePresentation : PresentationState := {
  sense := .minimize
  domainType := .const ``Nat []
  valueType := .const ``Nat []
  binders := #[{ name := `n, type := .const ``Nat [] }]
  objective := placeholder
  constraints := #[constraint `a, constraint `b, constraint `c]
}

private def replacement (index : Nat)
    (entries : Array ConstraintEntry) : ConstraintReplacement := {
  index
  entries
  pointwiseIff := placeholder
}

private def constraintNames (state : PresentationState) : Array Name :=
  state.constraints.map (·.name)

run_cmd do
  let .ok removed := basePresentation.applyDelta {
      constraintReplacements := #[replacement 1 #[]]
    }
    | throwError "zero-entry constraint replacement was rejected"
  expect (constraintNames removed == #[`a, `c])
    "zero-entry replacement did not remove exactly the selected constraint"

  let .ok replaced := basePresentation.applyDelta {
      constraintReplacements := #[replacement 1 #[constraint `x]]
    }
    | throwError "one-entry constraint replacement was rejected"
  expect (constraintNames replaced == #[`a, `x, `c])
    "one-entry replacement did not preserve surrounding order"

  let .ok expanded := basePresentation.applyDelta {
      constraintReplacements := #[replacement 1 #[constraint `x, constraint `y]]
    }
    | throwError "many-entry constraint replacement was rejected"
  expect (constraintNames expanded == #[`a, `x, `y, `c])
    "many-entry replacement did not splice entries in source order"

  let .ok replacedAndAdded := basePresentation.applyDelta {
      constraintReplacements := #[replacement 0 #[], replacement 1 #[constraint `x]]
      constraintAdditions := #[{
        entry := constraint `tail
        pointwiseIff := placeholder
      }]
    }
    | throwError "combined removal, replacement, and addition was rejected"
  expect (constraintNames replacedAndAdded == #[`x, `c, `tail])
    "removal, replacement, and addition did not preserve their specified order"

run_cmd do
  let duplicate : PresentationDelta := {
    constraintReplacements := #[
      replacement 0 #[constraint `x],
      replacement 0 #[constraint `y]
    ]
  }
  match basePresentation.applyDelta duplicate with
  | .error (.duplicateConstraintReplacement 0) => pure ()
  | _ => throwError "duplicate constraint replacements were not rejected"

  let outOfRange : PresentationDelta := {
    constraintReplacements := #[replacement 3 #[constraint `x]]
  }
  match basePresentation.applyDelta outOfRange with
  | .error (.constraintIndexOutOfBounds 3 3) => pure ()
  | _ => throwError "an out-of-range constraint replacement was not rejected"

/-! ## Terminal results and relation-driven certificates -/

private def terminalResult : StepResult := {
  nextSemantic := placeholder
  primitiveCertificate := placeholder
  presentationDelta := {}
  status := .terminal
  companions := #[{
    name := `terminalWitness
    type := .const ``True []
    value := placeholder
  }]
}

run_cmd do
  expect (terminalResult.status == .terminal)
    "terminal step status was not retained"
  expect (terminalResult.companions.size == 1)
    "terminal companion requests were not retained"
  match terminalResult.companions[0]? with
  | some companion =>
      expect (companion.name == `terminalWitness)
        "terminal companion request changed during construction"
  | none => throwError "terminal companion request disappeared"

run_cmd do
  let env ← Lean.getEnv
  let duplicate : Array DeclarationNameRequest := #[
    { name := `PTranTest.RunnerInternals.pending },
    { name := `PTranTest.RunnerInternals.pending }
  ]
  match preflightDeclarationNames env duplicate with
  | .error (.duplicate _) => pure ()
  | _ => throwError "duplicate companion/output declarations passed preflight"
  match preflightDeclarationNames env #[{ name := ``True }] with
  | .error (.alreadyDeclared _) => pure ()
  | _ => throwError "an existing global declaration passed preflight"
  match terminalResult.companions[0]? with
  | some companion =>
      match preflightDeclarationNames env #[companion.nameRequest] with
      | .ok _ => pure ()
      | .error _ => throwError "a fresh terminal companion failed preflight"
  | none => throwError "terminal companion request disappeared"

def SyntheticRelation (left right : Nat) : Prop :=
  left = right

theorem SyntheticRelation.reflexivity (value : Nat) :
    SyntheticRelation value value := rfl

theorem SyntheticRelation.transitivity {left middle right : Nat}
    (first : SyntheticRelation left middle)
    (second : SyntheticRelation middle right) :
    SyntheticRelation left right :=
  first.trans second

private def syntheticRunner : CertificateRunner where
  relation := ``SyntheticRelation
  refl := ``SyntheticRelation.reflexivity
  trans := ``SyntheticRelation.transitivity

run_cmd Lean.Elab.Command.liftTermElabM do
  let zero := Lean.mkNatLit 0
  let relationType ← syntheticRunner.relationType zero zero
  let reflexive ← syntheticRunner.reflexivity zero
  let reflexiveType ← Lean.Meta.inferType reflexive
  unless ← Lean.Meta.isDefEq reflexiveType relationType do
    throwError "the synthetic runner produced a certificate for the wrong relation"
  let composed ← syntheticRunner.compose reflexive reflexive
  Lean.Meta.check composed

/-! A typed runner commit checks its primitive certificate and normalization,
updates the semantic/presentation pair atomically, and retains terminal state. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let nat := Lean.mkConst ``Nat
  let objective ← Lean.Meta.withLocalDeclD `point nat fun point =>
    Lean.Meta.mkLambdaFVars #[point] point
  let feasible ← Lean.Meta.withLocalDeclD `point nat fun point =>
    Lean.Meta.mkLambdaFVars #[point] (Lean.mkConst ``True)
  let semantic ← Lean.Meta.mkAppM ``PTran.Problem.mk #[objective, feasible]
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let semantic ← Lean.instantiateMVars semantic
  let presentation : PresentationState := {
    sense := .minimize
    domainType := nat
    valueType := nat
    binders := #[{ name := `point, type := nat }]
    objective
  }
  let canonical ← presentation.canonicalProblem
  unless ← Lean.Meta.isDefEq semantic canonical do
    throwError "canonical empty-feasibility construction changed the problem"
  let semanticObjective ← Lean.Meta.mkAppM ``PTran.Problem.objective #[semantic]
  let canonicalObjective ← Lean.Meta.mkAppM ``PTran.Problem.objective #[canonical]
  let semanticFeasible ← Lean.Meta.mkAppM ``PTran.Problem.feasible #[semantic]
  let canonicalFeasible ← Lean.Meta.mkAppM ``PTran.Problem.feasible #[canonical]
  let objectiveEquality ← Lean.Meta.withLocalDeclD `point nat fun point => do
    let left := Lean.mkApp semanticObjective point
    let right := Lean.mkApp canonicalObjective point
    unless ← Lean.Meta.isDefEq left right do
      throwError "identity normalization changed the objective"
    Lean.Meta.mkLambdaFVars #[point] (← Lean.Meta.mkEqRefl left)
  let feasibleIff ← Lean.Meta.withLocalDeclD `point nat fun point => do
    let left := Lean.mkApp semanticFeasible point
    let right := Lean.mkApp canonicalFeasible point
    unless ← Lean.Meta.isDefEq left right do
      throwError "identity normalization changed feasibility"
    let proof := Lean.mkApp (Lean.mkConst ``Iff.rfl) left
    Lean.Meta.mkLambdaFVars #[point] proof
  let equivalence ← Lean.Meta.mkAppM ``PTran.pointwiseEquivalence
    #[semantic, canonical, objectiveEquality, feasibleIff]
  let normalization : PointwiseNormalization := {
    semantic
    canonical
    objectiveEquality
    feasibleIff
    equivalence
  }
  normalization.check
  let primitive ← globalEquivalenceRunner.reflexivity semantic
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let primitive ← Lean.instantiateMVars primitive
  let initial : RunnerState := {
    semantic
    canonical
    semanticDomainType := nat
    semanticValueType := nat
    presentation
    accumulatedCertificate := primitive
    normalization
  }
  let validDelta : PresentationDelta := {
    normalizationObjectiveEquality? := some objectiveEquality
    normalizationFeasibleIff? := some feasibleIff
  }
  let malformedEvidence : StepResult := {
    nextSemantic := semantic
    primitiveCertificate := primitive
    presentationDelta := {
      binderReplacements := #[{
        index := 0
        entry := presentation.binders[0]!
        typeEquality := Lean.mkConst ``True.intro
      }]
      normalizationObjectiveEquality? := some objectiveEquality
      normalizationFeasibleIff? := some feasibleIff
    }
  }
  let malformedRejected ← try
      discard <| initial.commit globalEquivalenceRunner malformedEvidence
      pure false
    catch _ => pure true
  unless malformedRejected do
    throwError "the typed runner accepted malformed presentation evidence"
  let result : StepResult := {
    nextSemantic := semantic
    primitiveCertificate := primitive
    presentationDelta := validDelta
    status := .terminal
    companions := #[{
      name := `PTranTest.RunnerInternals.committedCompanion
      type := Lean.mkConst ``True
      value := Lean.mkConst ``True.intro
    }]
  }
  let .ok committed ← initial.commit globalEquivalenceRunner result
    | throwError "a valid typed identity step did not commit"
  unless committed.status == .terminal do
    throwError "typed commit discarded terminal status"
  unless committed.companions.size == 1 do
    throwError "typed commit discarded a companion declaration"
  let finalCertificate ← committed.finalCertificate globalEquivalenceRunner
  Lean.Meta.check finalCertificate
  let rejected ← try
      discard <| committed.commit globalEquivalenceRunner result
      pure false
    catch _ => pure true
  unless rejected do
    throwError "the typed runner accepted a step after terminal status"

end PTranTest.RunnerInternals
