import PTran.Elab.Reformulation
import Mathlib.Data.Nat.Basic

/-!
# Reformulation name allocation

Visible-name comparison, independent name inventories, and deterministic
freshening are checked through the runner API without the public DSL.
-/

namespace PTranTest.Reformulation.NameAllocation

open Lean
open PTran.Elab.Reformulation

private def expect (condition : Bool) (message : String) :
    Lean.Elab.Command.CommandElabM Unit :=
  unless condition do
    throwError message

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

end PTranTest.Reformulation.NameAllocation
