/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.NLP.Form
import Morew.Elab.NLP.Rewrite
import Morew.Elab.Reformulation.Replace
import Morew.Elab.Rewrite.Decomposition
import Morew.Elab.Rewrite.Direct
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Whole-problem smooth-NLP planning

Bare `nlp` certifies smooth rows before considering exact direct-bound rules.
The objective is retained and certified against the final feasibility predicate.
Accepted row data and its analytic evidence survive later auxiliary insertions;
normalization to scalar residuals belongs to the form, not the presentation.

Only a successful local rewrite splits an original conjunction group. Failed
rows are retried after later rewrites expose useful domain evidence. Every
successful rewrite supplies fully certified replacement rows, so this process
never recursively peels a generated nonsmooth expression or loops on a rule.
-/

namespace Morew.Elab.NLP.Terminal

open Lean Lean.Meta
open Morew.Elab.Reformulation
open Morew.Elab.Rewrite

/-- A complete terminal result, before allocating visible names or declarations. -/
structure Result where
  /-- Final typed presentation retaining accepted comparison predicates. -/
  presentation : PresentationState
  /-- Exact equivalence from the incoming canonical problem. -/
  equivalence : Expr
  /-- Checked smooth-NLP data representing the final canonical problem. -/
  form : Expr
  /-- Original presentation index of each final entry. -/
  rowOrigins : Array Nat
  /-- Original entries split or replaced by exact lowering. -/
  replacedIndices : Array Nat
  /-- Origin and type of each appended auxiliary, in binder order. -/
  auxiliaries : Array (Nat × Expr)

/-- Rebase terminal evidence before command materialization. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result := {
  result with
  presentation := result.presentation.replaceFVars oldVars newVars
  equivalence := result.equivalence.replaceFVars oldVars newVars
  form := result.form.replaceFVars oldVars newVars
  auxiliaries := result.auxiliaries.map fun (origin, type) =>
    (origin, type.replaceFVars oldVars newVars)
}

private structure Work where
  presentation : PresentationState
  equivalence : Expr
  rowOrigins : Array Nat
  certifiedRows : Array (Option Rows.Result)
  replacedIndices : Array Nat := #[]
  auxiliaries : Array (Nat × Expr) := #[]
  nextName : Nat := 0

private def splice (entries : Array α) (index : Nat) (replacement : Array α) : Array α :=
  entries.extract 0 index ++ replacement ++ entries.extract (index + 1) entries.size

private partial def freshPlaceholder (inventory : NameInventory) (index : Nat) : Name × Nat :=
  let name := Name.mkSimple s!"_terminalNLP_{index}"
  if inventory.contains .decisionBinder name || inventory.contains .constraintLabel name then
    freshPlaceholder inventory (index + 1)
  else (name, index + 1)

private def feasibility (presentation : PresentationState) : MetaM Expr := do
  mkAppM ``Morew.Problem.feasible #[← presentation.canonicalProblem]

-- The checked replacement's backward map is the identity or first projection.
-- Check that precise map before using it to transport a cached domain proof.
private def backwardFeasibility (old : PresentationState) (nextDomain : Expr)
    (auxiliary? : Option Expr) (replacement : Replace.RewriteResult) : MetaM Expr := do
  let nextFeasible ← mkAppM ``Morew.Problem.feasible #[replacement.targetProblem]
  let oldFeasible ← feasibility old
  let backward ← mkAppM ``Morew.GlobalEquivalence.backward #[replacement.equivalence]
  let map ← mkAppM ``Morew.GlobalImprovement.map #[backward]
  withLocalDeclD `point nextDomain fun point =>
    withLocalDeclD `feasible (mkApp nextFeasible point) fun hypothesis => do
      let packed ← mkAppOptM ``Subtype.mk
        #[some nextDomain, some nextFeasible, some point, some hypothesis]
      let evidence ← mkAppM ``Subtype.property #[mkApp map packed]
      let original ← if auxiliary?.isSome then mkAppM ``Prod.fst #[point] else pure point
      unless ← isDefEq (← inferType evidence) (mkApp oldFeasible original) do
        throwError "terminal NLP replacement changed its backward decision map"
      mkLambdaFVars #[point, hypothesis] evidence

private def applyReplacement (work : Work) (index : Nat) (rows : Array Expr)
    (certificates : Array (Option Rows.Result)) (nextDomain : Expr)
    (auxiliary? : Option Expr) (replacement : Replace.RewriteResult) : MetaM Work := do
  unless certificates.size == rows.size do
    throwError "terminal NLP replacement certificates do not match its generated rows"
  let old := work.presentation
  let origin := work.rowOrigins[index]!
  let nextFeasible ← mkAppM ``Morew.Problem.feasible #[replacement.targetProblem]
  let backward ← backwardFeasibility old nextDomain auxiliary? replacement
  let retainedCertificates ← work.certifiedRows.mapM fun certificate? =>
    certificate?.mapM (fun certificate => certificate.transport nextFeasible backward auxiliary?)
  let mut nextName := work.nextName
  let mut binders := old.binders
  let mut auxiliaries := work.auxiliaries
  let (objective, retained) ← match auxiliary? with
    | none => pure (old.objective, old.constraints)
    | some auxiliary => do
      let (name, following) := freshPlaceholder old.nameInventory nextName
      nextName := following
      binders := binders.push { name, type := auxiliary }
      auxiliaries := auxiliaries.push (origin, auxiliary)
      withLocalDeclD `point nextDomain fun point => do
        let original ← mkAppM ``Prod.fst #[point]
        let objective ← mkLambdaFVars #[point] (mkApp old.objective original)
        let retained ← old.constraints.mapM fun entry => do
          return { entry with predicate := ← mkLambdaFVars #[point] (mkApp entry.predicate original) }
        pure (objective, retained)
  let mut entries : Array ConstraintEntry := #[]
  for row in rows do
    let (name, following) := freshPlaceholder old.nameInventory nextName
    nextName := following
    entries := entries.push { name, predicate := row, ref := old.constraints[index]!.ref }
  let presentation := {
    old with domainType := nextDomain, binders, objective
             constraints := splice retained index entries }
  unless ← isDefEq (← presentation.canonicalProblem) replacement.targetProblem do
    throwError "terminal NLP presentation does not match the checked replacement"
  let equivalence ← instantiateMVars (← mkAppM ``Morew.GlobalEquivalence.trans
    #[work.equivalence, replacement.equivalence])
  return {
    presentation, equivalence
    rowOrigins := splice work.rowOrigins index (rows.map fun _ => origin)
    certifiedRows := splice retainedCertificates index certificates
    replacedIndices := if work.replacedIndices.contains origin then work.replacedIndices
      else work.replacedIndices.push origin
    auxiliaries, nextName }

private def applyPrepared (work : Work) (index : Nat) (prepared : Rewrite.Result) : MetaM Work := do
  let replacement ← Replace.applyReplacement work.presentation index prepared.toResult
  applyReplacement work index prepared.rowPredicates
    (prepared.rowPredicates.mapIdx fun i _ => some (prepared.certified.select i))
    prepared.nextDomain prepared.auxiliary? replacement

-- Use the NLP reduction boundary, never the affine helper-expansion policy.
private def decompose (domain predicate : Expr) : MetaM (Array Expr × Expr) :=
  withLocalDeclD `point domain fun point => do
    let (bodies, proof) ← Decomposition.split (mkApp predicate point)
      (fun body => Expr.reduceStructure body (preserveLets := true)
        (opaqueProblemDependencies? := some point))
    let predicates ← bodies.toArray.mapM (mkLambdaFVars #[point])
    let proof ← instantiateMVars (← mkLambdaFVars #[point] proof)
    checkWithKernel proof
    return (predicates, proof)

-- Splitting is speculative: retain the original named group unless one of its
-- leaves actually needs and admits a fully certified automatic replacement.
private def tryGroupCore (work : Work) (index : Nat) : MetaM (Option Work) := do
  let source := work.presentation.constraints[index]!.predicate
  let (leaves, decomposition) ← decompose work.presentation.domainType source
  if leaves.isEmpty then return none
  if leaves.size == 1 && (← isDefEq leaves[0]! source) then return none
  let retained := splice (work.presentation.constraints.map (·.predicate)) index #[]
  let conditional ← withLocalDeclD `point work.presentation.domainType fun point => do
    let remainder := Decomposition.conjunction (retained.toList.map (mkApp · point))
    withLocalDeclD `retained remainder fun hypothesis =>
      mkLambdaFVars #[point, hypothesis] (mkApp decomposition point)
  let replacement ← Replace.rewriteConstraintContextual work.presentation index leaves conditional
  let mut split ← applyReplacement work index leaves (leaves.map fun _ => none)
    work.presentation.domainType none replacement
  for offset in [:leaves.size] do
    let position := index + offset
    let predicate := split.presentation.constraints[position]!.predicate
    match ← Rows.certifyRows (← feasibility split.presentation) #[predicate] with
    | .ok certified =>
      split := { split with certifiedRows := split.certifiedRows.set! position (some certified) }
    | .error _ =>
      let retained := splice (split.presentation.constraints.map (·.predicate)) position #[]
      match ← Rewrite.plan predicate retained (insertionIndex := position) with
      | .ok prepared => return some (← applyPrepared split position prepared)
      | .error _ => pure ()
  return none

private def tryGroup (work : Work) (index : Nat) : MetaM (Option Work) := do
  let result : Except Unit Work ← State.withIsolatedMVars do
    match ← tryGroupCore work index with
    | some next => return .ok next
    | none => return .error ()
  return result.toOption

private def originalError (original : PresentationState) (origin : Nat)
    (error : Domain.DomainError) (ruleError : Rewrite.Error) : MetaM Domain.DomainError := do
  let label := original.constraints[origin]!.name.eraseMacroScopes
  return { error with
    rowIndex? := some origin
    reason := ← addMessageContext m!"constraint `{label}` is not certified as a smooth NLP by the available rules: {error.reason}\nexact rewriting: {ruleError.reason}\nuse `nlp at {label}` or `nlp at {label} using ruleName` before `nlp`; expose nested nonsmooth occurrences with an explicit epigraph or hypograph step" }

-- A surface reduction is accepted only for directly smooth leaves. Retrying
-- after accepted reductions lets a later guard provide domain evidence to an
-- earlier row without exposing unsuccessful reductions to rule discovery.
private partial def normalizeDirectRows (work : Work) (reduce : Expr → MetaM Expr) : MetaM Work := do
  let feasible ← feasibility work.presentation
  let constraints ← work.presentation.constraints.mapIdxM fun index row => do
    if work.certifiedRows[index]!.isSome then return row
    let predicate ← Direct.normalizePredicate row.predicate reduce
      (fun candidate => return (← Rows.certifyRows feasible #[candidate]).isOk)
      (opaqueProblemDependencies := true)
    return { row with predicate }
  if constraints.map (·.predicate) == work.presentation.constraints.map (·.predicate) then
    return work
  let presentation := { work.presentation with constraints }
  unless ← isDefEq (← presentation.canonicalProblem) (← work.presentation.canonicalProblem) do
    throwError "direct NLP normalization changed feasibility"
  normalizeDirectRows { work with presentation } reduce

private partial def lower (original : PresentationState) (work : Work)
    (reduce? : Option (Expr → MetaM Expr)) : MetaM (Except Domain.DomainError Work) := do
  let work ← match reduce? with
    | some reduce => normalizeDirectRows work reduce
    | none => pure work
  let mut work := work
  let mut firstError? := none
  for index in [:work.presentation.constraints.size] do
    if work.certifiedRows[index]!.isSome then continue
    let predicate := work.presentation.constraints[index]!.predicate
    match ← Rows.certifyRows (← feasibility work.presentation) #[predicate] with
    | .ok certified =>
      work := { work with certifiedRows := work.certifiedRows.set! index (some certified) }
    | .error rowError =>
      let retained := splice (work.presentation.constraints.map (·.predicate)) index #[]
      match ← Rewrite.plan predicate retained (insertionIndex := index) with
      | .ok prepared => return ← lower original (← applyPrepared work index prepared) reduce?
      | .error ruleError =>
        if let some next ← tryGroup work index then return ← lower original next reduce?
        if firstError?.isNone then
          firstError? := some (← originalError original work.rowOrigins[index]! rowError ruleError)
  match firstError? with
  | some error => return .error error
  | none => return .ok work

private def planCore (presentation : PresentationState) (reduce? : Option (Expr → MetaM Expr)) :
    MetaM (Except Domain.DomainError Result) := do
  let canonical ← presentation.canonicalProblem
  let work : Work := {
    presentation
    equivalence := ← mkAppM ``Morew.GlobalEquivalence.refl #[canonical]
    rowOrigins := presentation.constraints.mapIdx fun index _ => index
    certifiedRows := presentation.constraints.map fun _ => none }
  let work ← match ← lower presentation work reduce? with
    | .ok work => pure work
    | .error error => return .error error
  -- Final feasibility can expose margins only after exact row lowering. Check
  -- the complete reduced objective against that predicate, then let buildForm
  -- combine its domain with the already certified row domains as usual.
  let work ← match reduce? with
    | none => pure work
    | some reduce => do
      let feasible ← feasibility work.presentation
      let objective ← Direct.normalize work.presentation.objective reduce fun candidate => do
        let canonical ← { work.presentation with objective := candidate }.canonicalProblem
        let realObjective ← mkAppOptM ``Morew.Problem.objective
          #[some work.presentation.domainType, some (mkConst ``Real), some canonical]
        return (← Domain.certifyWithEvidence feasible #[realObjective] Rows.factsProvider).isOk
      pure { work with presentation := { work.presentation with objective } }
  let form ← match ← buildForm work.presentation work.certifiedRows with
    | .ok form => pure form
    | .error error =>
      let suggestion := if error.sourceIndex?.isSome then
          match presentation.sense with
          | .minimize => "use an explicit `epigraph t` or occurrence lift before `nlp` for a nonsmooth objective"
          | .maximize => "use an explicit `hypograph t` or occurrence lift before `nlp` for a nonsmooth objective"
        else "check every retained constraint and its domain evidence"
      let reason ← addMessageContext
        m!"not certified as a smooth NLP by the available rules: {error.reason}; {suggestion}"
      return .error { error with reason }
  checkWithKernel work.equivalence
  checkWithKernel form
  return .ok {
    presentation := work.presentation, equivalence := work.equivalence, form
    rowOrigins := work.rowOrigins
    replacedIndices := work.replacedIndices.qsort (· < ·)
    auxiliaries := work.auxiliaries }

/-- Plan deterministic exact lowering and certify the complete final problem.
No visible names or declarations are emitted. Failures restore caller state.
An optional surface reducer is admitted only after direct certification; failed
reductions never enter registered matching. -/
def plan (presentation : PresentationState) (reduce? : Option (Expr → MetaM Expr) := none) :
    MetaM (Except Domain.DomainError Result) :=
  State.withIsolatedMVars do
    try
      for expression in #[presentation.domainType, presentation.valueType, presentation.objective] ++
          presentation.binders.map (·.type) ++ presentation.constraints.map (·.predicate) do
        unless ← Domain.Evidence.complete expression do
          throwError "terminal NLP validation requires fully elaborated expressions without placeholders"
      let mut instances := #[]
      for source in #[presentation.objective] ++ presentation.constraints.map (·.predicate) do
        for inst in ← Expr.sourceFiniteInstances source do
          unless instances.contains inst do instances := instances.push inst
      Morew.Elab.Rewrite.Plan.withScopedFiniteInstances
        (fun result oldVars newVars => result.map
          (fun (value : Result) => value.replaceFVars oldVars newVars))
        instances.toList (planCore presentation reduce?)
    catch error =>
      return .error {
        source := presentation.objective, expression := presentation.objective
        type := ← inferType presentation.objective, kind := .invalidInstance
        reason := ← addMessageContext
          m!"not certified as a smooth NLP by the available rules: {error.toMessageData}" }

end Morew.Elab.NLP.Terminal
