/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Lean.Meta.Basic
import Lean.Meta.Transform
import Lean.Meta.Match.MatcherInfo
import Qq

/-!
# Shared expression inspection for proof-producing elaborators

These utilities inspect local dependencies, unresolved metavariables, structural
presentations, and supported real-space shapes. Structural reduction preserves
named arithmetic and user function heads; source finiteness discovery never
expands named helpers or promotes evidence mentioning a source binder.
-/

namespace Morew.Elab.Expr

open Lean Lean.Meta Qq

/-- An unsupported expression together with a diagnostic retaining its context. -/
structure Error where
  /-- The smallest expression at which recognition failed. -/
  expression : Expr
  /-- Explanation, including the pretty-printing context of the expression. -/
  reason : MessageData

instance : ToMessageData Error := ⟨(·.reason)⟩

/-- Inspect dependence on a local decision variable and unresolved metavariables,
following referenced local declaration values and types. Merely checking `hasFVar`
misses dependencies hidden behind a local let or an instance. -/
partial def inspectLocals (expression : Expr) (point? : Option FVarId)
    (seen : FVarIdSet := {}) : MetaM (Bool × Bool) := do
  let expression ← instantiateMVars expression
  let mut dependent := false
  let mut unresolved := expression.hasMVar
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    if point? == some id then dependent := true
    unless seen.contains id do
      seen := seen.insert id
      if let some declaration := (← getLCtx).find? id then
        let (dep, hole) ← inspectLocals declaration.type point? seen
        dependent := dependent || dep
        unresolved := unresolved || hole
        if let some value := declaration.value? (allowNondep := true) then
          let (dep, hole) ← inspectLocals value point? seen
          dependent := dependent || dep
          unresolved := unresolved || hole
  return (dependent, unresolved)

/-- Whether an expression depends on the decision free variable, following
local declaration values and types as well as resolved metavariables. -/
def depends (point expression : Expr) : MetaM Bool := do
  return (← inspectLocals expression (some point.fvarId!)).1

/-- Check for unresolved metavariables, including those hidden in the types or
values of referenced local declarations. Shared by proof-producing recognizers. -/
def hasUnresolved (expression : Expr) : MetaM Bool := do
  return (← inspectLocals expression none).2

/-- Reduce local lets, applications, projections, and compiler-generated tuple
matches while preserving named arithmetic and user function heads.

Only problem-container fields and single-alternative product matchers may
unfold named declarations. This is internal support for typed presentations.
With `preserveLets`, stop at a head let so the caller can retain its evidence
and local instances while recognizing the body. When `opaqueProblemDependencies?`
is supplied, named problem containers depending on that local variable remain
opaque; inline structural containers are still reduced.
-/
partial def reduceStructure (expression : Expr) (preserveLets : Bool := false)
    (opaqueProblemDependencies? : Option Expr := none) : MetaM Expr := do
  let expression := (← instantiateMVars expression).consumeMData
  match expression with
  | .letE _ _ value body _ =>
    if preserveLets then pure expression
    else reduceStructure (body.instantiate1 value) false opaqueProblemDependencies?
  | .fvar id =>
    if let some value := (← id.getDecl).value? (allowNondep := true) then
      reduceStructure value preserveLets opaqueProblemDependencies?
    else pure expression
  | .proj name index value =>
    let value ← reduceStructure value preserveLets opaqueProblemDependencies?
    if let .letE binding type value body nondep := value then
      -- Move only the projection through a preserved let. Recognition can then
      -- inspect its evidence in the original scope before reducing the body.
      pure (.letE binding type value (.proj name index body) nondep)
    else if value.isAppOf ``Prod.mk then
      reduceStructure value.getAppArgs[index + 2]! preserveLets opaqueProblemDependencies?
    else pure (.proj name index value)
  | .app .. =>
    let arguments := expression.getAppArgs
    let function ← reduceStructure expression.getAppFn preserveLets opaqueProblemDependencies?
    if let .letE name type value body nondep := function then
      return ← reduceStructure (.letE name type value
        (mkAppN body (arguments.map (·.liftLooseBVars 0 1))) nondep)
        preserveLets opaqueProblemDependencies?
    if function.isLambda then
      return ← reduceStructure (function.beta arguments) preserveLets opaqueProblemDependencies?
    if (function.isConstOf ``Prod.casesOn || function.isConstOf ``Prod.rec) &&
        arguments.size >= 5 then
      let value := arguments[if function.isConstOf ``Prod.casesOn then 3 else 4]!
      let branch := arguments[if function.isConstOf ``Prod.casesOn then 4 else 3]!
      let fields := #[Expr.proj ``Prod 0 value, Expr.proj ``Prod 1 value]
      return ← reduceStructure (mkAppN (branch.beta fields)
        (arguments.extract 5 arguments.size)) preserveLets opaqueProblemDependencies?
    if let some name := function.constName? then
      if let some matcher ← getMatcherInfo? name then
        if matcher.numAlts == 1 && arguments.size >= matcher.arity then
          let mut productsOnly := decide (matcher.numDiscrs > 0)
          for i in [matcher.getFirstDiscrPos:matcher.getFirstAltPos] do
            let type ← whnf (← inferType arguments[i]!)
            productsOnly := productsOnly && type.isAppOfArity ``Prod 2
          if productsOnly then
            let declaration ← getConstInfo name
            if let some value := declaration.value? then
              let value := value.instantiateLevelParams
                declaration.levelParams function.constLevels!
              return ← reduceStructure (value.beta arguments)
                preserveLets opaqueProblemDependencies?
    if (function.isConstOf ``Prod.fst || function.isConstOf ``Prod.snd) &&
        arguments.size >= 3 then
      let projection := .proj ``Prod
        (if function.isConstOf ``Prod.fst then 0 else 1) arguments[2]!
      return ← reduceStructure (mkAppN projection (arguments.extract 3 arguments.size))
        preserveLets opaqueProblemDependencies?
    if (function.isConstOf ``Morew.Problem.objective ||
        function.isConstOf ``Morew.Problem.feasible) && arguments.size >= 3 then
      -- The model declaration is the container being inspected; its objective
      -- and constraint function heads remain intact after selecting the field.
      let problem ← match opaqueProblemDependencies? with
        | some point =>
          if ← depends point arguments[2]! then
            reduceStructure arguments[2]! preserveLets opaqueProblemDependencies?
          else whnf arguments[2]!
        | none => whnf arguments[2]!
      if problem.isAppOf ``Morew.Problem.mk then
        let index := if function.isConstOf ``Morew.Problem.objective then 2 else 3
        return ← reduceStructure (mkAppN problem.getAppArgs[index]!
          (arguments.extract 3 arguments.size)) preserveLets opaqueProblemDependencies?
    return mkAppN function arguments
  | _ => pure expression

/-- Recognize exactly a real Euclidean space indexed by `Fin n`, including aliases. -/
def euclideanDimension? (type : Expr) : MetaM (Option Expr) := do
  let shape ← whnf type
  unless shape.isAppOfArity ``WithLp 2 do return none
  unless ← isDefEq shape.getAppArgs[0]! q((2 : ENNReal)) do return none
  let coordinates ← whnf shape.getAppArgs[1]!
  let .forallE _ index body _ := coordinates | return none
  let body ← Core.betaReduce (← whnf body)
  if body.hasLooseBVars then return none
  unless body.isConstOf ``Real do return none
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 do return none
  return some index.getAppArgs[0]!

/-- Whether a type has the supported real/Euclidean/product/finite-function shape. -/
partial def isSupportedSpace (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isConstOf ``Real then return true
  if (← euclideanDimension? type).isSome then return true
  if type.isAppOfArity ``Prod 2 then
    return (← isSupportedSpace type.getAppArgs[0]!) &&
      (← isSupportedSpace type.getAppArgs[1]!)
  if let .forallE _ index body _ := type then
    let body ← Core.betaReduce (← whnf body)
    if body.hasLooseBVars || (← isProp index) then return false
    -- Shape validation needs finiteness, not an enumeration in the ambient
    -- context. Indexed operations retain their own elaborated Fintype instance.
    let finiteType ← mkAppM ``Finite #[index]
    unless (← synthInstance? finiteType).isSome do return false
    return ← isSupportedSpace body
  return false

/-- Recover finiteness proofs from `Finite` evidence and `Fintype` indexing
instances already present in the typed source. Local lets are substituted, but
named helpers are not expanded.
Instances mentioning a source binder are never promoted into the caller's scope.
Only `Finite` proofs are collected: each operation keeps its own enumeration. -/
def sourceFiniteInstances (source : Expr) : MetaM (Array Expr) := do
  let mut pending := [source]
  let mut seen : ExprSet := {}
  let mut instances := #[]
  while let expression :: rest := pending do
    pending := rest
    if seen.contains expression then continue
    seen := seen.insert expression
    let expression ← if expression.hasLooseBVars then
        pure expression.consumeMData.headBeta
      else reduceStructure expression (preserveLets := true)
    unless expression.hasLooseBVars do
      -- Inspect the elaborated type rather than operation names or the spelling
      -- of a let annotation. This also handles aliased classes and coefficients
      -- such as Fintype.card, without expanding their definitions.
      let type ← whnf (← inferType expression)
      if type.isAppOfArity ``Finite 1 then
        unless instances.contains expression do
          instances := instances.push expression
      else if type.isAppOfArity ``Fintype 1 then
        let proof ← mkAppOptM ``Finite.of_fintype
          #[some type.getAppArgs[0]!, some expression]
        unless instances.contains proof do
          instances := instances.push proof
    match expression with
    | .letE _ _ value body _ => pending := value :: body.instantiate1 value :: pending
    | .lam _ _ body _ | .forallE _ _ body _ => pending := body :: pending
    | .app f a => pending := f :: a :: pending
    | .proj _ _ value => pending := value :: pending
    | .mdata _ value => pending := value :: pending
    | _ => pure ()
  return instances

end Morew.Elab.Expr
