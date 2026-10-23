import Morew.Elab.Reformulation
import Mathlib.Data.Nat.Basic

/-!
# Reformulation runner certificates and terminal state

The typed runner composes certificates for its configured relation, validates
presentation evidence, retains companion declarations, and rejects steps after
a terminal result.
-/

namespace MorewTest.Reformulation.RunnerState

open Lean
open Morew.Elab.Reformulation

private def expect (condition : Bool) (message : String) :
    Lean.Elab.Command.CommandElabM Unit :=
  unless condition do
    throwError message

private def placeholder : Expr := .const ``True.intro []

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
    { name := `MorewTest.Reformulation.RunnerState.pending },
    { name := `MorewTest.Reformulation.RunnerState.pending }
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
  let semantic ← Lean.Meta.mkAppM ``Morew.Problem.mk #[objective, feasible]
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
  let semanticObjective ← Lean.Meta.mkAppM ``Morew.Problem.objective #[semantic]
  let canonicalObjective ← Lean.Meta.mkAppM ``Morew.Problem.objective #[canonical]
  let semanticFeasible ← Lean.Meta.mkAppM ``Morew.Problem.feasible #[semantic]
  let canonicalFeasible ← Lean.Meta.mkAppM ``Morew.Problem.feasible #[canonical]
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
  let equivalence ← Lean.Meta.mkAppM ``Morew.pointwiseEquivalence
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
      name := `MorewTest.Reformulation.RunnerState.committedCompanion
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

end MorewTest.Reformulation.RunnerState
