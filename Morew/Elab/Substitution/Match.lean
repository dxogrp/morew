/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Substitution.Registry
import Morew.Elab.Substitution.Evidence
import Morew.Elab.Expr
import Morew.Elab.State

/-! Match complete coordinate maps under rigid retained and fresh binders.
Use independent evidence for premises and source feasibility for range coverage.
Certify each candidate in isolation before resolving ambiguity. -/

namespace Morew.Elab.Substitution.Match

open Lean Lean.Meta

/-- A matched parameterization and checked pointwise range evidence. -/
structure Result where
  /-- Fully instantiated record for the complete coordinate map. -/
  rule : Expr
  /-- Proof of `rule.range retained selected` at the source point. -/
  rangeProof : Expr

-- Reduce binding syntax while keeping mathematical helpers closed.
private def structuralTree (expression : Expr) : MetaM Expr :=
  Meta.transform expression (pre := fun expression => do
    let reduced ← Registry.structural expression
    if reduced != expression then return .visit reduced
    return .continue)

private partial def matchValue (expected actual : Expr)
    (rigid : Array Expr := #[]) : MetaM Unit := do
  let expected ← Registry.structural expected
  let actual ← Registry.structural actual
  if expected.isMVar || expected.getAppFn.isMVar then
    let actual ← structuralTree actual
    let arguments ← expected.getAppArgs.mapM structuralTree
    for binder in rigid do
      if (← Expr.depends binder actual) &&
          !(← arguments.anyM (Expr.depends binder)) then
        throwError "coordinate parameter depends on a rigid binder outside its arguments: {actual}"
    unless ← isDefEq expected actual do
      throwError "coordinate parameter does not match {actual}"
    return
  let type ← inferType expected
  if (← isProp type) || ((← isType expected) && !(← isProp expected)) ||
      (← isClass? type).isSome then
    unless ← isDefEq expected actual do
      throwError "unsupported coordinate type or operation instance in {actual}"
    return
  match expected, actual with
  | .lam _ domain body _, .lam _ otherDomain otherBody _ =>
    unless ← isDefEq domain otherDomain do
      throwError "coordinate map binder types differ"
    withLocalDeclD `coordinate domain fun coordinate =>
      matchValue (body.instantiate1 coordinate) (otherBody.instantiate1 coordinate)
        (rigid.push coordinate)
  | .lam _ domain body _, _ =>
    withLocalDeclD `coordinate domain fun coordinate =>
      matchValue (body.instantiate1 coordinate) (mkApp actual coordinate)
        (rigid.push coordinate)
  | _, .lam _ domain body _ =>
    withLocalDeclD `coordinate domain fun coordinate =>
      matchValue (mkApp expected coordinate) (body.instantiate1 coordinate)
        (rigid.push coordinate)
  | .forallE _ domain body _, .forallE _ otherDomain otherBody _ =>
    matchValue domain otherDomain rigid
    withLocalDeclD `coordinate domain fun coordinate =>
      matchValue (body.instantiate1 coordinate) (otherBody.instantiate1 coordinate)
        (rigid.push coordinate)
  | .proj name index value, .proj otherName otherIndex otherValue =>
    unless name == otherName && index == otherIndex do
      throwError "coordinate expression {expected} does not match {actual}"
    matchValue value otherValue rigid
  | .const name _, .const otherName _ =>
    unless name == otherName && (← isDefEq expected actual) do
      throwError "coordinate expression {expected} does not match {actual}"
  | _, _ =>
    if expected.isApp || actual.isApp then
      let sameHead := match expected.getAppFn, actual.getAppFn with
        | .const a _, .const b _ => a == b
        | a, b => a == b
      unless sameHead && expected.getAppNumArgs == actual.getAppNumArgs do
        throwError "coordinate operation {expected} does not match {actual}"
      let expectedArgs := expected.getAppArgs
      let actualArgs := actual.getAppArgs
      for i in [:expectedArgs.size] do matchValue expectedArgs[i]! actualArgs[i]! rigid
    else unless expected == actual do
      throwError "coordinate expression {expected} does not match {actual}"

private def solveParameter (point argument : Expr) : MetaM Unit := do
  let argument ← instantiateMVars argument
  unless argument.isMVar do return
  let type ← instantiateMVars (← inferType argument)
  if type.hasMVar then return
  if (← isClass? type).isSome then
    if let some inst ← synthInstance? type then
      unless ← Expr.depends point inst do argument.mvarId!.assign inst
  else if ← isProp type then
    if let some proof ← Evidence.proveIndependent? point type then
      argument.mvarId!.assign proof

private def attempt {α : Type} (map point retained selected feasibleEvidence original : Expr)
    (accept : Result → MetaM α) : MetaM α := do
  if (← Expr.hasUnresolved map) || (← Expr.depends point map) then
    throwError "coordinate map contains unresolved parameters or depends on the source point"
  let (parameters, _, type) ← forallMetaTelescopeReducing (← inferType original)
  let rule := mkAppN original parameters
  let (retainedType, _, oldType, expectedMap) ← Registry.parameterization type
  unless ← isDefEq retainedType (← inferType retained) do
    throwError "parameterization retained-coordinate type does not match"
  unless ← isDefEq oldType (← inferType selected) do
    throwError "parameterization original-coordinate type does not match"
  unless ← isDefEq (← inferType expectedMap) (← inferType map) do
    throwError "parameterization coordinate-map type does not match"
  matchValue expectedMap map
  for argument in parameters do solveParameter point argument
  let rule ← instantiateMVars rule
  if ← Expr.hasUnresolved rule then
    throwError "coordinate parameterization contains unresolved parameters or independent premises"
  if ← Expr.depends point rule then
    throwError "coordinate parameterization depends on the source point; feasible conditions belong in its range"
  unless ← isDefEq (← inferType rule) (← mkAppM ``Morew.CoordinateParameterization #[map]) do
    throwError "parameterization does not describe the complete coordinate map"
  checkWithKernel rule
  let goal ← mkAppM ``Morew.CoordinateParameterization.range #[rule, retained, selected]
  let some proof ← Evidence.proveRange? point goal feasibleEvidence
    | do
      let obligation ← Evidence.predicateView goal 32
      let obligation ← Meta.transform obligation (post := fun expression => do
        return .done (← Registry.structural expression))
      throwError "cannot establish coordinate coverage from the source constraints: {obligation}"
  unless ← isDefEq (← inferType proof) goal do
    throwError "coordinate coverage evidence proves the wrong proposition"
  checkWithKernel proof
  accept { rule, rangeProof := proof }

private def checked {α : Type} (map point retained selected feasibleEvidence : Expr)
    (prepare : MetaM Expr) (accept : Result → MetaM α) : MetaM α := do
  let result : Except Exception α ← State.withIsolatedMVars do
    try return .ok (← attempt map point retained selected feasibleEvidence (← prepare) accept)
    catch error => return .error error
  match result with
  | .ok result => return result
  | .error error => throw error

/-- Match only the supplied parameterization, without registry fallback. The
complete consumer certificate is included in the isolated attempt. -/
def rule {α : Type} (map point retained selected feasibleEvidence expression : Expr)
    (accept : Result → MetaM α) : MetaM α :=
  checked map point retained selected feasibleEvidence (pure expression) accept

/-- Instantiate only the selected declaration, registered or unregistered. -/
def declaration {α : Type} (map point retained selected feasibleEvidence : Expr)
    (name : Name) (accept : Result → MetaM α) : MetaM α :=
  checked map point retained selected feasibleEvidence (mkConstWithFreshMVarLevels name) accept

/-- Certify every matching declaration and require one distinct success. Each
candidate sees the same environment; only the selected proof dependencies survive. -/
def discover {α : Type} (map point retained selected feasibleEvidence : Expr)
    (accept : Result → MetaM α) : MetaM α := do
  let result : Except Exception α ← State.withIsolatedMVars do
    try
      let candidates ← Registry.candidates map
      let environment ← getEnv
      let mut successes : Array (Name × α × Environment) := #[]
      let mut failures : Array MessageData := #[]
      for name in candidates do
        try
          let result ← declaration map point retained selected feasibleEvidence name accept
          successes := successes.push (name, result, ← getEnv)
        catch error => failures := failures.push m!"{name}: {error.toMessageData}"
        setEnv environment
      if let [(_, selected, environment)] := successes.toList then
        setEnv environment
        return .ok selected
      if successes.size > 1 then
        let names := successes.toList.map (·.1.toString)
        throwError "ambiguous coordinate parameterizations: {String.intercalate ", " names}; select one with `via`"
      if failures.isEmpty then
        throwError "no registered coordinate parameterization matches the replacement map"
      throwError "no registered coordinate parameterization was fully certified:\n{MessageData.joinSep failures.toList "\n"}"
    catch error => return .error error
  match result with
  | .ok result => return result
  | .error error => throw error

end Morew.Elab.Substitution.Match
