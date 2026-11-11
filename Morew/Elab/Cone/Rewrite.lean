/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Cone.Rules
import Morew.Elab.Evidence.Sign
import Morew.Elab.Cone.Plan
import Morew.Elab.Cone.MatrixDomain
import Morew.Elab.Evidence
import Morew.Elab.Rewrite.Match
import Morew.Elab.Expr
import Morew.Elab.State

/-! Select and certify exact conic replacements.
Automatic selection requires a unique success after preferring the built-in SOC
norm rule over the power-norm rule. Explicit selection bypasses that preference.
Retained constraints supply rule premises. -/

namespace Morew.Elab.Cone.Rewrite

open Lean Lean.Meta Qq
open Morew.Elab.Rewrite

private theorem dimensionPositive (n : Nat) [Nonempty (Fin n)] : 0 < n :=
  Fin.pos_iff_nonempty.mpr inferInstance

private theorem dimensionPositiveOfNe (n : Nat) (h : n ≠ 0) : 0 < n :=
  Nat.pos_of_ne_zero h

private def nonemptyEvidence? (point dimension : Expr) : MetaM (Option Expr) := do
  if (← Expr.depends point dimension) || (← Morew.Elab.Rewrite.Plan.unresolved dimension) then return none
  let n : Q(Nat) := dimension
  let goal : Q(Prop) := q(0 < $n)
  let nonzero : Q(Prop) := q($n ≠ 0)
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let evidence := declaration.toExpr
    if (← Expr.depends point evidence) || (← Morew.Elab.Rewrite.Plan.unresolved evidence) then continue
    if ← isDefEq declaration.type goal then return some evidence
    if ← isDefEq declaration.type nonzero then
      return some (← mkAppM ``dimensionPositiveOfNe #[dimension, evidence])
  let saved ← saveState
  try
    let proof ← mkAppOptM ``dimensionPositive #[some dimension, none]
    if ← Morew.Elab.Rewrite.Plan.unresolved proof then throwError "unresolved finite nonemptiness"
    unless ← isDefEq (← inferType proof) goal do throwError "invalid dimension evidence"
    checkWithKernel proof
    return some proof
  catch _ => saved.restore
  if let some value ← getNatValue? (← Expr.reduceStructure dimension) then
    if value > 0 && value ≤ 100000 then return some (← mkDecideProof goal)
  return none

private partial def canonicalRealRange (goal : Expr) : MetaM Bool := do
  let goal ← Expr.reduceStructure goal
  if goal.isAppOfArity ``And 2 then
    return (← canonicalRealRange goal.getAppArgs[0]!) &&
      (← canonicalRealRange goal.getAppArgs[1]!)
  unless goal.isAppOfArity ``LT.lt 4 || goal.isAppOfArity ``LE.le 4 do return false
  let args := goal.getAppArgs
  unless ← isDefEq args[0]! q(ℝ) do return false
  let left : Q(ℝ) := args[2]!
  let right : Q(ℝ) := args[3]!
  let canonical : Q(Prop) := if goal.isAppOfArity ``LT.lt 4 then q($left < $right)
    else q($left ≤ $right)
  isDefEq goal canonical

/-- Use bounded conic evidence from predicates other than the selected row. -/
private def proveObligation (point : Expr) (retained : Array Expr)
    (evidence goal : Expr) : MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  if ← Morew.Elab.Rewrite.Plan.unresolved goal then return none
  if let some proof ← Evidence.proveIndependent? point goal then return some proof
  let reduced ← Expr.reduceStructure goal
  if reduced.isAppOf ``Matrix.IsSymm then
    if let some proof ← Symmetry.prove? point reduced.getAppArgs.back! then
      let proof := mkApp proof point
      unless ← isDefEq (← inferType proof) goal do return none
      checkWithKernel proof
      return some proof
    throwError "registered conic rewrite was not certified: missing global matrix symmetry; required {goal} at every decision point"
  if reduced.isAppOf ``Matrix.PosDef then
    if let some proof ← MatrixDomain.prove? point reduced retained evidence then return some proof
    throwError "registered conic rewrite was not certified: missing positive-definiteness evidence for the matrix argument; required {goal}; supply a positive-definite domain constraint, independent proof, positive PSD margin, or retained identity-block PSD witness"
  if let .forallE name indexType body _ := reduced then
    let indexType ← whnf indexType
    unless indexType.isAppOfArity ``Fin 1 do return none
    if ← Expr.depends point indexType then return none
    return ← withLocalDeclD name indexType fun index => do
      let body ← Expr.reduceStructure (body.instantiate1 index)
      unless body.isAppOfArity ``LT.lt 4 || body.isAppOfArity ``LE.le 4 do return none
      let args := body.getAppArgs
      unless ← isDefEq args[0]! q(ℝ) do return none
      let strict := body.isAppOfArity ``LT.lt 4
      let value : Q(ℝ) := args[3]!
      let canonical : Q(Prop) := if strict then q(0 < $value) else q(0 ≤ $value)
      unless ← isDefEq body canonical do return none
      let some proof ← Evidence.Sign.signFromRetained? point value retained evidence strict (some index)
        | throwError "registered conic rewrite was not certified: missing coordinatewise {if strict then "positive" else "nonnegative"} constant margin at {index}; required an independent ε with {if strict then "0 < ε" else "0 ≤ ε"} and a retained constraint ε ≤ {value}"
      let proof ← mkLambdaFVars #[index] proof
      unless ← isDefEq (← inferType proof) goal do return none
      checkWithKernel proof
      return some proof
  if reduced.isAppOfArity ``LT.lt 4 || reduced.isAppOfArity ``LE.le 4 then
    let args := reduced.getAppArgs
    let strict := reduced.isAppOfArity ``LT.lt 4
    if ← isDefEq args[0]! q(ℝ) then
      let value : Q(ℝ) := args[3]!
      let canonical : Q(Prop) := if strict then q(0 < $value) else q(0 ≤ $value)
      if ← isDefEq reduced canonical then
        if let some proof ← Evidence.Sign.signFromRetained? point value retained evidence strict then
          return some proof
        throwError "registered conic rewrite was not certified: missing {if strict then "positive" else "nonnegative"} constant margin; required an independent ε with {if strict then "0 < ε" else "0 ≤ ε"} and a retained constraint ε ≤ {value}"
    if strict && (← isDefEq args[0]! q(Nat)) then
      let n : Q(Nat) := args[3]!
      if ← isDefEq reduced q(0 < $n) then
        if let some proof ← nonemptyEvidence? point n then return some proof
        throwError "registered conic rewrite was not certified: missing independent nonempty dimension evidence (0 < {n})"
  if !(← Expr.depends point goal) && (← canonicalRealRange reduced) then
    throwError "registered conic rewrite was not certified: missing independent real-parameter evidence; required {goal}"
  return none

-- Apply conic structural reduction before registry matching.
private def matchingBody (expression : Expr) : MetaM Expr := do
  Meta.transform expression (pre := fun value => do
    let reduced ← Expr.reduceStructure value (preserveLets := true)
    if reduced != value then return .visit reduced
    return .continue)

private def materialize (source domain point evidence : Expr) (retained : Array Expr)
    (matched : Match.Result) (provider : Affine.EvidenceProvider) : MetaM Plan.Result := do
  let auxiliary ← whnf (← instantiateMVars matched.auxiliary)
  if ← Expr.depends point auxiliary then throwError "the auxiliary type depends on an optimization variable"
  let target ← withLocalDeclD `auxiliary auxiliary fun auxiliary => do
    let body ← Plan.exposeTarget (mkApp matched.target auxiliary)
    let reduceProjection (value : Expr) : MetaM TransformStep := do
      if value.isProj || value.isAppOf ``Subtype.val ||
          value.isAppOf ``Prod.fst || value.isAppOf ``Prod.snd then
        let reduced ← Registry.structural value
        if reduced != value then return .visit reduced
      return .continue
    let body ← Meta.transform body (pre := reduceProjection) (post := reduceProjection)
    mkLambdaFVars #[auxiliary] body
  let certificate ← Morew.Elab.Rewrite.Plan.closeCertificate source point evidence
    auxiliary target matched.sourceIff
  Plan.finish source domain certificate retained provider

private def attempt (source : Expr) (retained : Array Expr)
    (matchRule : Expr → Expr → (Expr → MetaM (Option Expr)) →
      (Match.Result → MetaM Plan.Result) → MetaM Plan.Result)
    (provider : Affine.EvidenceProvider) : MetaM (Except Expr.Error Plan.Result) :=
  State.withIsolatedMVars do
    try
      if ← Morew.Elab.Rewrite.Plan.unresolved source then throwError "unresolved metavariables in selected predicate"
      let domain ← Morew.Elab.Rewrite.Plan.predicateDomain source
      for row in retained do
        if ← Morew.Elab.Rewrite.Plan.unresolved row then throwError "unresolved metavariables in retained constraints"
        unless ← isDefEq (← Morew.Elab.Rewrite.Plan.predicateDomain row) domain do
          throwError "retained constraint has a different decision domain"
      let mut instances ← Expr.sourceFiniteInstances source
      for row in retained do instances := instances ++ (← Expr.sourceFiniteInstances row)
      let result ← Morew.Elab.Rewrite.Plan.withScopedFiniteInstances Plan.Result.replaceFVars instances.toList do
        withLocalDeclD `point domain fun point =>
          Morew.Elab.Rewrite.Plan.withScopedEvidence Plan.Result.replaceFVars point (mkApp source point) do
            let bodies := retained.map (mkApp · point)
            withLocalDecl `retained .default (mkAndN bodies.toList)
                (kind := .implDetail) fun evidence => do
              let body ← matchingBody (mkApp source point)
              matchRule point body (proveObligation point bodies evidence) fun matched =>
                materialize source domain point evidence retained matched provider
      return .ok result
    catch error =>
      return .error { expression := source, reason := ← addMessageContext error.toMessageData }

/-- Certify an explicitly named declaration without fallback. -/
def planDeclaration (source : Expr) (name : Name) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Plan.Result) :=
  State.withIsolatedMVars do
    Finite.withHelperFiniteInstances Plan.Result.replaceFVars (#[source] ++ retained) do
      attempt source retained
        (fun point body prove accept =>
          Match.declaration point body name accept prove) provider

/-- Match graph and bound records with their operation instances.
Adapt whole-predicate certificates directly, retrying subtype conditions by typed matching. -/
def planExplicit (source rule : Expr) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Plan.Result) :=
  State.withIsolatedMVars do
    Finite.withHelperFiniteInstances Plan.Result.replaceFVars (#[source] ++ retained) do
      if (← whnf (← inferType rule)).isAppOfArity ``Morew.ConstraintRepr 2 then
        let direct ← Plan.plan source rule provider
        if let .ok result := direct then return .ok result
      attempt source retained
        (fun point body prove accept =>
          Match.rule point body rule accept prove) provider

private structure CertifiedCandidate where
  name : Name
  result : Plan.Result
  environment : Environment

/-- Prefer the built-in SOC norm rule when both built-in norm rules certify.
Leave explicit selection and other candidates unchanged. -/
private def preferSecondOrderNorm (successes : Array CertifiedCandidate) :
    Array CertifiedCandidate :=
  if successes.any (·.name == ``Morew.Conic.SecondOrder.normEpigraph) then
    successes.filter (·.name != ``Morew.Conic.Power.normEpigraph)
  else successes

/-- Certify candidates from the same environment, apply the norm preference, and require
one success. Retain only the selected candidate's auxiliary declarations. -/
def planUnique (predicate : Expr) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Plan.Result) :=
  State.withIsolatedMVars do
    try
      if ← Morew.Elab.Rewrite.Plan.unresolved predicate then
        throwError "unresolved metavariables in selected predicate"
      let domain ← Morew.Elab.Rewrite.Plan.predicateDomain predicate
      let lookup ← withLocalDeclD `point domain fun point => do
        mkLambdaFVars #[point] (← matchingBody (mkApp predicate point))
      let candidates ← Registry.candidates .conic lookup
      let environment ← getEnv
      let mut successes : Array CertifiedCandidate := #[]
      let mut failures : Array MessageData := #[]
      for name in candidates do
        match ← planDeclaration predicate name retained provider with
        | .ok result => successes := successes.push ⟨name, result, ← getEnv⟩
        | .error error => failures := failures.push m!"{name}: {error.reason}"
        setEnv environment
      successes := preferSecondOrderNorm successes
      if let [selected] := successes.toList then
        setEnv selected.environment
        return .ok selected.result
      if successes.size > 1 then
        let names := successes.toList.map (·.name.toString)
        throwError "ambiguous exact conic rules: {String.intercalate ", " names}; select one with `using`"
      if failures.isEmpty then
        throwError "no supported registered conic rule matches the entire selected predicate and bound polarity"
      throwError "no registered exact conic rule was fully certified:\n{MessageData.joinSep failures.toList "\n"}"
    catch error => return .error {
      expression := predicate
      reason := ← addMessageContext error.toMessageData }

end Morew.Elab.Cone.Rewrite
