/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rules
import Morew.Elab.Conic.Domain
import Morew.Elab.Rewrite.Match
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Checked exact conic rewriting

Automatic discovery and explicit certificate selection share checked matching and
conic target certification. Every automatic candidate comes from `@[morew_conic]`, including built-ins.
Both targeted and terminal callers require one fully certified replacement.
Retained evidence can discharge domain obligations for same-domain replacements;
conditional auxiliary lifts remain outside this API.
-/

namespace Morew.Elab.Conic.Rewrite

open Lean Lean.Meta Qq
open Morew.Elab.Rewrite

private theorem existsUnitIff (p : Unit → Prop) : (∃ u, p u) ↔ p () := by
  constructor
  · rintro ⟨⟨⟩, h⟩
    exact h
  · exact fun h => ⟨(), h⟩

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

/-- Evidence for registered records uses the established bounded conic policy.
The selected row is never among the supplied retained predicates. -/
private def proveObligation (point : Expr) (retained : Array Expr)
    (evidence goal : Expr) : MetaM (Option Expr) := do
  let goal ← instantiateMVars goal
  if ← Morew.Elab.Rewrite.Plan.unresolved goal then return none
  for declaration in ← getLCtx do
    let proof := declaration.toExpr
    if (← Expr.depends point proof) || (← Morew.Elab.Rewrite.Plan.unresolved proof) then continue
    if ← isDefEq declaration.type goal then
      checkWithKernel proof
      return some proof
  let reduced ← Expr.reduceStructure goal
  if reduced.isAppOfArity ``LT.lt 4 || reduced.isAppOfArity ``LE.le 4 then
    let args := reduced.getAppArgs
    let strict := reduced.isAppOfArity ``LT.lt 4
    if ← isDefEq args[0]! q(ℝ) then
      let value : Q(ℝ) := args[3]!
      let canonical : Q(Prop) := if strict then q(0 < $value) else q(0 ≤ $value)
      if ← isDefEq reduced canonical then
        if let some proof ← Domain.signFromRetained? point value retained evidence strict then
          return some proof
        throwError "registered conic rewrite was not certified: missing {if strict then "positive" else "nonnegative"} constant margin; required an independent ε with {if strict then "0 < ε" else "0 ≤ ε"} and a retained constraint ε ≤ {value}"
    if strict && (← isDefEq args[0]! q(Nat)) then
      let n : Q(Nat) := args[3]!
      if ← isDefEq reduced q(0 < $n) then
        if let some proof ← nonemptyEvidence? point n then return some proof
        throwError "registered conic rewrite was not certified: missing independent nonempty dimension evidence (0 < {n})"
  return none

-- Preserve the conic consumer's structural policy without teaching the neutral
-- registry about model containers or compiler-generated product matchers.
private def matchingBody (expression : Expr) : MetaM Expr := do
  Meta.transform expression (pre := fun value => do
    let reduced ← Expr.reduceStructure value (preserveLets := true)
    if reduced != value then return .visit reduced
    return .continue)

private def materialize (source domain point evidence : Expr) (retained : Array Expr)
    (matched : Match.Result) (provider : Affine.EvidenceProvider) : MetaM Plan.Prepared := do
  let auxiliary ← whnf (← instantiateMVars matched.auxiliary)
  if ← Expr.depends point auxiliary then throwError "the auxiliary type depends on a decision variable"
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
  let proof ← instantiateMVars matched.sourceIff
  if ← Expr.depends evidence target then
    throwError "generated cone rows depend on retained feasibility evidence"
  if !(← Expr.depends evidence proof) then
    let target ← mkLambdaFVars #[point] target
    let pointwise ← mkLambdaFVars #[point] proof
    let lift ← mkAppM ``Morew.ExactConstraintLift.mk #[auxiliary, target, pointwise]
    let lift ← Morew.Elab.Rewrite.Plan.checkLift source lift
    return .inl (← Plan.finish source domain lift provider)
  unless ← isDefEq auxiliary (mkConst ``Unit) do
    throwError "retained-context exact replacements with auxiliary variables are not supported"
  let raw := mkApp target (mkConst ``Unit.unit)
  let eliminated ← mkAppM ``Iff.trans #[proof, ← mkAppM ``existsUnitIff #[target]]
  let (rows, decomposition) ← Plan.splitTarget raw
  let rowPredicates ← rows.toArray.mapM fun row => mkLambdaFVars #[point] row
  let conditionalIff ← mkLambdaFVars #[point, evidence]
    (← mkAppM ``Iff.trans #[eliminated, decomposition])
  if ← Morew.Elab.Rewrite.Plan.unresolved conditionalIff then
    throwError "registered conic certificate contains unresolved metavariables"
  checkWithKernel conditionalIff
  let certifiedRows ← Plan.certifyRows rowPredicates provider
  Plan.prepareContextual source retained { domain, rowPredicates, certifiedRows, conditionalIff }

private def attempt (source : Expr) (retained : Array Expr)
    (matchRule : Expr → Expr → (Expr → MetaM (Option Expr)) →
      (Match.Result → MetaM Plan.Prepared) → MetaM Plan.Prepared)
    (provider : Affine.EvidenceProvider) : MetaM (Except Expr.Error Plan.Prepared) :=
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
      let result ← Morew.Elab.Rewrite.Plan.withScopedFiniteInstances Plan.Prepared.replaceFVars instances.toList do
        withLocalDeclD `point domain fun point =>
          Morew.Elab.Rewrite.Plan.withScopedEvidence Plan.Prepared.replaceFVars point (mkApp source point) do
            let bodies := retained.map (mkApp · point)
            withLocalDeclD `retained (Decomposition.conjunction bodies.toList) fun evidence => do
              let body ← matchingBody (mkApp source point)
              matchRule point body (proveObligation point bodies evidence) fun matched =>
                materialize source domain point evidence retained matched provider
      return .ok result
    catch error =>
      return .error { expression := source, reason := ← addMessageContext error.toMessageData }

/-- Select an explicitly named declaration, registered or not. There is no
fallback to any other rule when matching, exactness, or affine checking fails. -/
def planDeclaration (source : Expr) (name : Name) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Plan.Prepared) :=
  State.withIsolatedMVars do
    Plan.withHelperFiniteInstances Plan.Prepared.replaceFVars (#[source] ++ retained) do
      attempt source retained
        (fun point body prove accept => Match.declaration point body name accept prove) provider

/-- Preserve the checked whole-predicate adapter for concrete certificate
expressions. If that adapter cannot prepare the record, typed matching may
reconstruct subtype inputs using the existing retained-domain policy. Both
attempts use exactly the supplied record; registered rules are never searched. -/
def planExplicit (source rule : Expr) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Plan.Prepared) :=
  State.withIsolatedMVars do
    Plan.withHelperFiniteInstances Plan.Prepared.replaceFVars (#[source] ++ retained) do
      let direct ← Plan.plan source rule provider
      if let .ok result := direct then return .ok (.inl result)
      attempt source retained
        (fun point body prove accept => Match.rule point body rule accept prove) provider

/-- Certify all registered candidates and require a unique success. -/
def planUnique (predicate : Expr) (retained : Array Expr := #[])
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Plan.Prepared) :=
  State.withIsolatedMVars do
    try
      if ← Morew.Elab.Rewrite.Plan.unresolved predicate then
        throwError "unresolved metavariables in selected predicate"
      let domain ← Morew.Elab.Rewrite.Plan.predicateDomain predicate
      let lookup ← withLocalDeclD `point domain fun point => do
        mkLambdaFVars #[point] (← matchingBody (mkApp predicate point))
      let candidates ← Registry.candidates .conic lookup
      let mut successes : Array (Name × Plan.Prepared) := #[]
      let mut failures : Array MessageData := #[]
      for name in candidates do
        match ← planDeclaration predicate name retained provider with
        | .ok result => successes := successes.push (name, result)
        | .error error => failures := failures.push m!"{name}: {error.reason}"
      if let [(_, result)] := successes.toList then return .ok result
      if successes.size > 1 then
        let names := successes.toList.map fun (name, _) => name.toString
        throwError "ambiguous exact conic rules: {String.intercalate ", " names}; select one with `using`"
      if failures.isEmpty then
        throwError "no supported registered conic rule matches the entire selected predicate and bound polarity"
      throwError "no registered exact conic rule was fully certified:\n{MessageData.joinSep failures.toList "\n"}"
    catch error => return .error {
      expression := predicate
      reason := ← addMessageContext error.toMessageData }

end Morew.Elab.Conic.Rewrite
