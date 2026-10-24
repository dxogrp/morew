/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Lean.Meta.Basic

/-!
# Reformulation name allocation

Visible-name allocation and exact global declaration-name preflight.
-/

namespace Morew.Elab.Reformulation

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

/-! ## Global declaration names -/

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


end Morew.Elab.Reformulation
