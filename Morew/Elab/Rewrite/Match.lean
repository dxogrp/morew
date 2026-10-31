/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Rewrite.Registry
import Morew.Elab.Rewrite.Plan
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Checked matching of exact representations

Matching preserves the operation spelling of the selected predicate. It exposes
local binding syntax and representation fields, not the implementations of
mathematical helpers. Product and subtype representation inputs are reconstructed
from the matched operands; a consumer may supply checked evidence for subtype
conditions. Evidence provision never changes the selected source predicate.
-/

namespace Morew.Elab.Rewrite.Match

open Lean Lean.Meta

/-- A pointwise checked replacement, still in the caller's evidence scope. -/
structure Result where
  /-- The checked, decision-independent auxiliary space. -/
  auxiliary : Expr
  /-- The replacement predicate on an auxiliary value at the current point. -/
  target : Expr
  /-- Exactness for the complete original predicate at the current point. -/
  sourceIff : Expr
  /-- Whether the consumer's controlled evidence callback supplied a proof. -/
  usedEvidence : Bool := false

/-- Consumer-controlled proof search; no retained assumptions are used by default. -/
abbrev Prove := Expr → MetaM (Option Expr)

private partial def inputValue (type : Expr) (depth : Nat := 0) :
    MetaM (Expr × Array Expr) := do
  if depth > 32 then throwError "representation input structure is too deeply nested"
  let type ← whnf type
  if type.isAppOfArity ``Prod 2 then
    let (first, firstProofs) ← inputValue type.getAppArgs[0]! (depth + 1)
    let (second, secondProofs) ← inputValue type.getAppArgs[1]! (depth + 1)
    return (← mkAppM ``Prod.mk #[first, second], firstProofs ++ secondProofs)
  if type.isAppOfArity ``Subtype 2 then
    let (value, proofs) ← inputValue type.getAppArgs[0]! (depth + 1)
    let proof ← mkFreshExprMVar (mkApp type.getAppArgs[1]! value)
    let input ← mkAppOptM ``Subtype.mk
      #[some type.getAppArgs[0]!, some type.getAppArgs[1]!, some value, some proof]
    return (input, proofs.push proof)
  return (← mkFreshExprMVar type, #[])

-- Concrete exact records describe the whole current point. A subtype domain
-- may add checked guards around that point, but cannot infer a different input
-- map. Nested guards are collected from the innermost carrier outwards.
private partial def subtypeInputValue (point type : Expr) (depth : Nat := 0) :
    MetaM (Expr × Array Expr) := do
  if depth > 32 then throwError "representation input structure is too deeply nested"
  if ← isDefEq type (← inferType point) then return (point, #[])
  let type ← whnf type
  unless type.isAppOfArity ``Subtype 2 do
    throwError "the exact representation subtype carrier is not the decision space"
  let (value, proofs) ← subtypeInputValue point type.getAppArgs[0]! (depth + 1)
  let proof ← mkFreshExprMVar (mkApp type.getAppArgs[1]! value)
  let input ← mkAppOptM ``Subtype.mk
    #[some type.getAppArgs[0]!, some type.getAppArgs[1]!, some value, some proof]
  return (input, proofs.push proof)

private def normalizeComparison (expression : Expr) : MetaM Expr :=
  Comparison.normalize expression (fun e => Registry.structural e)

-- Fixed data parameters may compute to the same value, including section
-- parameters such as `n + 0` and `n`. Mathematical coordinates, functions,
-- types, proofs, and instances keep their separate typed syntax checks.
-- Data-value comparison occurs only below an already matched operation,
-- never at a comparison endpoint.
private def sameFixedDataValue (point expected actual type : Expr) : MetaM Bool := do
  if (← Expr.hasUnresolved expected) || (← Expr.hasUnresolved actual) then return false
  let type ← whnf type
  if type.isSort || type.isForall || (← isProp type) ||
      (← isClass? type).isSome || (← Expr.isSupportedSpace type) then return false
  let some name := type.getAppFn.constName? | return false
  let some (.inductInfo _) := (← getEnv).find? name | return false
  if (← Expr.depends point expected) || (← Expr.depends point actual) then return false
  withNewMCtxDepth <| isDefEq expected actual

-- Value syntax is matched before definitional equality. In particular, an
-- opaque/named helper cannot accidentally match its unfolded implementation.
private partial def matchValue (point expected actual : Expr)
    (operationArgument : Bool := false) : MetaM Unit := do
  let expected ← Registry.structural expected
  let actual ← Registry.structural actual
  if expected.isMVar then
    unless ← isDefEq (← inferType expected) (← inferType actual) do
      throwError "representation input types differ at {actual}"
    expected.mvarId!.assign actual
    return
  if expected.getAppFn.isMVar then
    unless ← isDefEq expected actual do
      throwError "representation input does not match {actual}"
    return
  let type ← inferType expected
  if operationArgument && (← sameFixedDataValue point expected actual type) then return
  if (← isProp type) || ((← isType expected) && !(← isProp expected)) ||
      (← isClass? type).isSome then
    unless ← isDefEq expected actual do
      if type.isAppOf ``LE || type.isAppOf ``LT then
        throwError "unsupported order instance in {actual}"
      throwError "unsupported type or instance in {actual}"
    return
  -- Reconstructed inputs may be matched against an intact pair or subtype.
  -- Project only their fields; the surrounding mathematical head stays opaque.
  if expected.isAppOfArity ``Prod.mk 4 || expected.isAppOfArity ``Subtype.mk 4 then
    unless ← isDefEq type (← inferType actual) do
      throwError "representation input types differ at {actual}"
    let structureName := if expected.isAppOfArity ``Prod.mk 4 then ``Prod else ``Subtype
    let fields := expected.getAppArgs
    matchValue point fields[2]! (.proj structureName 0 actual)
    matchValue point fields[3]! (.proj structureName 1 actual)
    return
  match expected, actual with
  | .lam _ type body _, .lam _ otherType otherBody _ =>
    matchValue point type otherType
    withLocalDeclD `index type fun index =>
      matchValue point (body.instantiate1 index) (otherBody.instantiate1 index)
  | .lam _ type body _, _ =>
    withLocalDeclD `index type fun index =>
      matchValue point (body.instantiate1 index) (mkApp actual index)
  | _, .lam _ type body _ =>
    withLocalDeclD `index type fun index =>
      matchValue point (mkApp expected index) (body.instantiate1 index)
  | .forallE _ type body _, .forallE _ otherType otherBody _ =>
    -- Implication antecedents are proposition-valued binder domains; compare
    -- their mathematical heads just like the body, while ordinary types retain
    -- the type/instance comparison above.
    matchValue point type otherType
    withLocalDeclD `index type fun index =>
      matchValue point (body.instantiate1 index) (otherBody.instantiate1 index)
  | .proj name index value, .proj otherName otherIndex otherValue =>
    unless name == otherName && index == otherIndex do
      throwError "representation expression {expected} does not match {actual}"
    matchValue point value otherValue
  | .const name _, .const otherName _ =>
    unless name == otherName && (← isDefEq expected actual) do
      throwError "representation expression {expected} does not match {actual}"
  | _, _ =>
    if expected.isApp || actual.isApp then
      let expectedFn := expected.getAppFn
      let actualFn := actual.getAppFn
      let sameHead := match expectedFn, actualFn with
        | .const a _, .const b _ => a == b
        | _, _ => expectedFn == actualFn
      unless sameHead && expected.getAppNumArgs == actual.getAppNumArgs do
        throwError "representation operation {expected} does not match {actual}"
      let first := expected.getAppArgs
      let second := actual.getAppArgs
      let comparison := expectedFn.isConstOf ``Eq || expectedFn.isConstOf ``LE.le ||
        expectedFn.isConstOf ``LT.lt || expectedFn.isConstOf ``GE.ge ||
        expectedFn.isConstOf ``GT.gt
      for index in [:first.size] do
        matchValue point first[index]! second[index]! (!comparison)
    else unless expected == actual do
      throwError "representation expression {expected} does not match {actual}"

private def solveProof (point proof : Expr) (prove? : Prove) : MetaM Bool := do
  let proof ← instantiateMVars proof
  unless proof.isMVar do return false
  let type ← instantiateMVars (← inferType proof)
  if type.hasMVar then return false
  if (← isClass? type).isSome then
    if let some inst ← synthInstance? type then
      proof.mvarId!.assign inst
      return false
  if ← isProp type then
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail ||
          (← Expr.depends point declaration.toExpr) do
        if ← isDefEq declaration.type type then
          proof.mvarId!.assign declaration.toExpr
          return false
    if let some evidence ← prove? type then
      unless ← isDefEq (← inferType evidence) type do
        throwError "supplied representation-domain evidence proves the wrong proposition"
      checkWithKernel evidence
      proof.mvarId!.assign evidence
      return true
  return false

private def checkIndependent (point : Expr) (arguments : Array Expr) : MetaM Unit := do
  for argument in arguments do
    let argument ← instantiateMVars argument
    let type ← instantiateMVars (← inferType argument)
    -- Instances, including Prop-valued classes, cannot acquire a decision-local
    -- interpretation through typeclass synthesis. Ordinary proof parameters
    -- instead come from the source itself, independent hypotheses, or the
    -- consumer's checked callback, whose use is recorded in the result.
    if (← isClass? type).isSome then
      if (← Expr.depends point type) || (← Expr.depends point argument) then
        throwError "representation instance depends on the decision variable: {argument}"
    else if !(← isProof argument) then
      if ← Expr.depends point type then
        throwError "representation parameter type depends on the decision variable: {type}"
      if (← Expr.depends point argument) && !(← Expr.isSupportedSpace type) then
        throwError "representation shape parameter depends on the decision variable: {argument}"

/-- Expose representation fields and binding syntax while retaining every
mathematical function and predicate head in the target. -/
def expose (expression : Expr) : MetaM Expr := do
  Meta.transform expression (pre := fun value => do
    let reduced ← Registry.structural value (preserveLets := true)
    let head := reduced.getAppFn.constName?
    let descriptor := match head with
      | some ``Morew.ExactConstraintLift.target => some (3, 1)
      | some ``Morew.GraphRepresentation.target => some (4, 1)
      | some ``Morew.EpigraphRepresentation.target => some (5, 1)
      | some ``Morew.HypographRepresentation.target => some (5, 1)
      | some ``Morew.ExactConstraintLift.Auxiliary => some (3, 0)
      | some ``Morew.GraphRepresentation.Auxiliary => some (4, 0)
      | some ``Morew.EpigraphRepresentation.Auxiliary => some (5, 0)
      | some ``Morew.HypographRepresentation.Auxiliary => some (5, 0)
      | _ => none
    if let some (prefixSize, field) := descriptor then
      let arguments := reduced.getAppArgs
      if arguments.size >= prefixSize then
        if let some value ← projectCore? (← whnf arguments[prefixSize - 1]!) field then
          return .visit (mkAppN value (arguments.extract prefixSize arguments.size))
    if reduced != value then return .visit reduced
    return .continue)

private inductive ExactInput where
  | infer | whole | subtypeWhole
  deriving BEq

private def attempt (point sourceBody originalRule : Expr) (prove? : Prove)
    (reverseGraph : Bool) (exactInput : ExactInput)
    (view? : Option Comparison.View := none) : MetaM (Except Exception Result) := do
  let (parameters, _, type) ← forallMetaTelescopeReducing (← inferType originalRule)
  let type ← whnf type
  let rule := mkAppN originalRule parameters
  let (family, inputType, _) ← Registry.representation type
  if view?.isSome && family == .exact then
    throwError "comparison adaptation requires a graph, epigraph, or hypograph representation"
  let (input, proofArguments) ← if family == .exact then
      match exactInput with
      | .whole => do
        unless ← isDefEq inputType (← inferType point) do
          throwError "the exact representation input is not the decision space"
        pure (point, #[])
      | .subtypeWhole => subtypeInputValue point inputType
      | .infer => inputValue inputType
    else inputValue inputType
  let prefixArgs := type.getAppArgs.map some
  let proof ← match family with
    | .exact => do
      mkAppOptM ``Morew.ExactConstraintLift.source_iff_exists
        (prefixArgs ++ #[some rule, some input])
    | .graph =>
      let output ← mkFreshExprMVar type.getAppArgs[1]!
      mkAppOptM ``Morew.GraphRepresentation.source_iff_exists
        (prefixArgs ++ #[some rule, some input, some output])
    | .epigraph =>
      let output ← mkFreshExprMVar type.getAppArgs[1]!
      mkAppOptM ``Morew.EpigraphRepresentation.source_iff_exists
        (prefixArgs ++ #[some rule, some input, some output])
    | .hypograph =>
      let output ← mkFreshExprMVar type.getAppArgs[1]!
      mkAppOptM ``Morew.HypographRepresentation.source_iff_exists
        (prefixArgs ++ #[some rule, some input, some output])
  let proofType ← whnf (← inferType proof)
  let mut expected ← normalizeComparison proofType.getAppArgs[0]!
  if reverseGraph then
    unless family == .graph do throwError "not a graph representation"
    expected := mkAppN expected.getAppFn
      #[expected.getAppArgs[0]!, expected.getAppArgs[2]!, expected.getAppArgs[1]!]
  let actual ← normalizeComparison (view?.map (·.predicate) |>.getD sourceBody)
  matchValue point expected actual
  try
    let mut usedEvidence := false
    for argument in parameters ++ proofArguments do
      usedEvidence := (← solveProof point argument prove?) || usedEvidence
    checkIndependent point parameters
    let proof ← instantiateMVars proof
    let proof ← if reverseGraph then do
        let lhs := actual.getAppArgs[1]!
        let rhs := actual.getAppArgs[2]!
        mkAppM ``Iff.trans #[← mkAppOptM ``eq_comm #[none, some lhs, some rhs], proof]
      else pure proof
    if ← Plan.unresolved proof then
      throwError "the representation contains unresolved parameters or missing domain evidence"
    let proof ← match view? with
      | some view => mkAppM ``Iff.trans #[view.sourceIff, proof]
      | none => pure proof
    let proofType ← whnf (← inferType proof)
    unless ← isDefEq proofType.getAppArgs[0]! sourceBody do
      throwError "the representation does not describe the entire selected predicate"
    let existsType ← whnf proofType.getAppArgs[1]!
    unless existsType.isAppOfArity ``Exists 2 do
      throwError "internal error: representation target is not existential"
    let auxiliary ← expose (← instantiateMVars existsType.getAppArgs[0]!)
    if ← Expr.depends point auxiliary then
      throwError "representation auxiliary type depends on the decision variable"
    checkWithKernel proof
    let target ← expose existsType.getAppArgs[1]!
    return .ok { auxiliary, target, sourceIff := proof, usedEvidence }
  catch error => return .error error

private def checked {α : Type} (point sourceBody : Expr) (prepare : MetaM Expr)
    (accept : Result → MetaM α) (prove? : Prove) (exactInput : ExactInput) : MetaM α := do
  -- Diagnose the furthest successful stage: operation matching, domain/proof
  -- validation, then target certification. An adapted domain failure should
  -- not be hidden behind the original negative head's shape mismatch.
  let result : Except (Nat × Exception) α ← State.withIsolatedMVars do
    let tryAttempt := fun reverse inputMode view? => State.withIsolatedMVars do
      let matched ← try attempt point sourceBody (← prepare) prove? reverse inputMode view?
        catch exception => return .error (0, exception)
      let matched ← match matched with
        | .ok matched => pure matched
        | .error exception => return .error (1, exception)
      try return .ok (← accept matched)
      catch exception => return .error (2, exception)
    match ← tryAttempt false exactInput none with
    | .ok value => return .ok value
    | .error original =>
      let expression ← prepare
      let (_, _, type) ← forallMetaTelescopeReducing (← inferType expression)
      let (family, inputType, _) ← Registry.representation type
      if family == .graph || family == .epigraph || family == .hypograph then
        let mut failure := original
        if family == .graph then
          -- Preserve both direct graph orientations before adapting any signs.
          match ← tryAttempt true exactInput none with
          | .ok value => return .ok value
          | .error next =>
            if failure.1 < next.1 then failure := next
        for view in (← Comparison.signedViews sourceBody
            (fun e => Registry.structural e)).toList.drop 1 do
          for reverse in (if family == .graph then [false, true] else [false]) do
            match ← tryAttempt reverse exactInput (some view) with
            | .ok value => return .ok value
            | .error next =>
              if failure.1 < next.1 then failure := next
        return .error failure
      let subtypeWhole := family == .exact &&
          (← whnf inputType).isAppOfArity ``Subtype 2 &&
          !(← isDefEq inputType (← inferType point))
      if exactInput == .whole && subtypeWhole then
        -- Retry only subtype wrappers around the same complete decision point.
        -- Concrete records never acquire declaration-style input inference.
        return ← tryAttempt false .subtypeWhole none
      if family == .exact && exactInput == .infer then
        -- Exact records retain the whole-input fallback for unused inputs or
        -- coordinates, including subtype guards around the complete point.
        match ← tryAttempt false
            (if subtypeWhole then .subtypeWhole else .whole) none with
        | .ok value => return .ok value
        | .error failure =>
          -- Prefer an actual target-certification failure to a mismatch.
          if original.1 < 2 && failure.1 == 2 then return .error failure
      return .error original
  match result with
  | .ok value => pure value
  | .error (_, error) => throw error

/-- Match and certify exactly the supplied record. Each alternative includes
`accept` in its isolated attempt, preserving only a successful result's proof
dependencies. Concrete exact lifts retain their whole-decision interpretation;
subtype wrappers may add checked guards around that same point. Graph
orientations and checked real negation views count as one candidate per record.
Whole-predicate lifts do not receive comparison adaptations. -/
def rule {α : Type} (point sourceBody expression : Expr)
    (accept : Result → MetaM α) (prove? : Prove := fun _ => pure none) : MetaM α :=
  checked point sourceBody (pure expression) accept prove? .whole

/-- Instantiate and certify a declaration, retrying graph orientation when its
first matched target cannot be certified. Fresh universes belong to each attempt. -/
def declaration {α : Type} (point sourceBody : Expr) (name : Name)
    (accept : Result → MetaM α) (prove? : Prove := fun _ => pure none) : MetaM α :=
  checked point sourceBody (mkConstWithFreshMVarLevels name) accept prove? .infer

end Morew.Elab.Rewrite.Match
