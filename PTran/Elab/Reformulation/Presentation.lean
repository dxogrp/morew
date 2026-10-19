import PTran.Elab.Reformulation.Names
import PTran.Syntax

/-!
# Typed reformulation presentations

Typed presentation entries, atomic deltas, structural validation, and rebasing.
-/

namespace PTran.Elab.Reformulation

open Lean Lean.Meta

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


end PTran.Elab.Reformulation
