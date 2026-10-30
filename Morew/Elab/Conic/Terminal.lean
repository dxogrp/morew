/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Elab.Conic.Rewrite
import Morew.Elab.Rewrite.Decomposition
import Morew.Elab.Conic.Form
import Morew.Elab.Conic.Normalize
import Morew.Elab.Reformulation.Replace
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Whole-problem exact conic planning

Plan all row rewrites before allocating surface names. Already-conic named
groups retain their boundaries; groups containing unsupported leaves are split
exactly so their affine siblings can supply retained domain evidence.
-/

namespace Morew.Elab.Conic.Terminal

open Lean Lean.Meta
open Morew.Elab.Rewrite
open Morew.Elab.Reformulation
open Morew.Elab.Reformulation.Replace

/-- A complete checked terminal transformation, before visible-name allocation. -/
structure Result where
  /-- Final typed presentation, with temporary names for generated entries. -/
  presentation : PresentationState
  /-- Exact equivalence from the incoming canonical problem to the final one. -/
  equivalence : Expr
  /-- A checked `Conic.Form` of the final canonical problem. -/
  form : Expr
  /-- Original presentation-entry index for every final constraint entry. -/
  rowOrigins : Array Nat
  /-- Original entries replaced by splitting or exact automatic lowering. -/
  replacedIndices : Array Nat
  /-- Original entries changed by final membership normalization. This alone
  does not require allocating new labels. -/
  changedBodies : Array Nat
  /-- Original entry and auxiliary type, in decision-binder append order. -/
  auxiliaries : Array (Nat × Expr)

/-- Rebase all terminal evidence onto a fresh section-variable context. -/
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
  certifiedRows : Array (Option (Array RowResult))
  replacedIndices : Array Nat := #[]
  changedBodies : Array Nat := #[]
  auxiliaries : Array (Nat × Expr) := #[]
  nextName : Nat := 0

private def splice (entries : Array α) (index : Nat) (replacement : Array α) : Array α :=
  entries.extract 0 index ++ replacement ++ entries.extract (index + 1) entries.size

private partial def freshPlaceholder (inventory : NameInventory) (index : Nat) : Name × Nat :=
  let name := Name.mkSimple s!"_terminalConic_{index}"
  if inventory.contains .decisionBinder name || inventory.contains .constraintLabel name then
    freshPlaceholder inventory (index + 1)
  else
    (name, index + 1)

private def certifyPredicateDetailed (predicate : Expr) (provider : Affine.EvidenceProvider) :
    MetaM (Except Expr.Error (Array RowResult)) := do
  let (leaves, _) ← decomposePredicate predicate
  let mut rows := #[]
  for leaf in leaves do
    match ← normalizeRow leaf provider with
    | .error error => return .error error
    | .ok row => rows := rows.push row
  return .ok rows

private def certifyPredicate (predicate : Expr) (provider : Affine.EvidenceProvider) :
    MetaM (Option (Array RowResult)) := do
  return (← certifyPredicateDetailed predicate provider).toOption

private noncomputable def pullbackConstraint {X A : Type*}
    [AddCommGroup X] [Module ℝ X]
    [AddCommGroup A] [Module ℝ A]
    (row : Morew.Conic.Constraint X) : Morew.Conic.Constraint (X × A) :=
  ⟨row.cone, row.map.comp AffineMap.fst⟩

-- Compose an accepted affine map with the product projection. Re-recognizing
-- its source syntax would lose independent proof lets from the original rule.
private def pullbackRow (domain auxiliary : Expr) (row : RowResult) : MetaM RowResult := do
  let nextDomain ← mkAppM ``Prod #[domain, auxiliary]
  let constraint ← Space.withCanonicalDomain domain do
    Space.withCanonicalDomain auxiliary do
      instantiateMVars (← mkAppOptM ``pullbackConstraint
        #[some domain, some auxiliary, none, none, none, none, some row.constraint])
  let pointwiseIff ← withLocalDeclD `point nextDomain fun point => do
    mkLambdaFVars #[point] (mkApp row.pointwiseIff (← mkAppM ``Prod.fst #[point]))
  let normalization? ← row.normalization?.mapM fun normalization => do
    withLocalDeclD `point nextDomain fun point => do
      let original ← mkAppM ``Prod.fst #[point]
      return { normalization with
        predicate := ← mkLambdaFVars #[point] (mkApp normalization.predicate original)
        pointwiseIff := ← mkLambdaFVars #[point] (mkApp normalization.pointwiseIff original) }
  checkWithKernel constraint
  checkWithKernel pointwiseIff
  return { constraint, pointwiseIff, normalization? }

/-- Apply the same domain pullback as the checked rewrite and retain original
entry provenance independently of the temporary presentation names. -/
private def applyReplacement (work : Work) (index : Nat) (rows : Array Expr)
    (certificates : Array (Option (Array RowResult)))
    (nextDomain : Expr) (auxiliary? : Option Expr)
    (rewrite : Replace.RewriteResult) : MetaM Work := do
  unless certificates.size == rows.size do
    throwError "terminal replacement certificates do not match the generated rows"
  let origin := work.rowOrigins[index]!
  let old := work.presentation
  let mut nextName := work.nextName
  let mut binders := old.binders
  let mut auxiliaries := work.auxiliaries
  let mut retainedCertificates := work.certifiedRows
  let (objective, retained) ← match auxiliary? with
    | none => pure (old.objective, old.constraints)
    | some auxiliary => do
      let (name, following) := freshPlaceholder old.nameInventory nextName
      nextName := following
      binders := binders.push { name, type := auxiliary }
      auxiliaries := auxiliaries.push (origin, auxiliary)
      retainedCertificates ← retainedCertificates.mapM fun rows? =>
        rows?.mapM (·.mapM (pullbackRow old.domainType auxiliary))
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
    old with
    domainType := nextDomain
    binders
    objective
    constraints := splice retained index entries
  }
  let canonical ← presentation.canonicalProblem
  unless ← isDefEq canonical rewrite.targetProblem do
    throwError "terminal rewrite presentation does not match its checked target"
  let equivalence ← instantiateMVars (← mkAppM ``Morew.GlobalEquivalence.trans
    #[work.equivalence, rewrite.equivalence])
  let replacedIndices := if work.replacedIndices.contains origin then work.replacedIndices
    else work.replacedIndices.push origin
  return {
    presentation
    equivalence
    rowOrigins := splice work.rowOrigins index (rows.map fun _ => origin)
    certifiedRows := splice retainedCertificates index certificates
    replacedIndices
    changedBodies := work.changedBodies
    auxiliaries
    nextName
  }

/-- Split all nonlinear groups before searching for exact rewrites. This makes
affine domain margins in the same original group available to sibling leaves. -/
private def splitNonconicGroups (work : Work) (provider : Affine.EvidenceProvider) : MetaM Work := do
  let mut work := work
  let mut index := 0
  while index < work.presentation.constraints.size do
    let source := work.presentation.constraints[index]!.predicate
    let (leaves, decomposition) ← decomposePredicate source
    if let some rows ← certifyPredicate source provider then
      work := { work with certifiedRows := work.certifiedRows.set! index (some rows) }
      index := index + 1
      continue
    -- An atomic unsupported row needs no structural rewrite yet.
    if leaves.size == 1 && (← isDefEq leaves[0]! source) then
      index := index + 1
      continue
    let presentation := work.presentation
    let retained := splice (presentation.constraints.map (·.predicate)) index #[]
    let conditional ← withLocalDeclD `point presentation.domainType fun point => do
      let remainder := Decomposition.conjunction (retained.toList.map (mkApp · point))
      withLocalDeclD `retained remainder fun hypothesis =>
        mkLambdaFVars #[point, hypothesis] (mkApp decomposition point)
    let rewrite ← rewriteConstraintContextual presentation index leaves conditional
    work ← applyReplacement work index leaves (leaves.map fun _ => none)
      presentation.domainType none rewrite
    index := index + leaves.size
  return work

private def applyPrepared (work : Work) (index : Nat) (prepared : Plan.Result) : MetaM Work := do
  let rewrite ← Morew.Elab.Reformulation.Replace.applyReplacement
    work.presentation index prepared.toResult
  applyReplacement work index prepared.rowPredicates
    (prepared.certifiedRows.map fun row => some #[row]) prepared.nextDomain prepared.auxiliary? rewrite

private def originalError (original : PresentationState) (origin : Nat)
    (error : Expr.Error) : MetaM Expr.Error := do
  let label := original.constraints[origin]!.name.eraseMacroScopes
  let reason ← addMessageContext
    m!"constraint `{label}`: {error.reason}\nunsupported expression: {error.expression}\nuse `conic at {label} using rule` with an exact representation before `conic`"
  return { error with reason }

private partial def lower (original : PresentationState) (work : Work)
    (provider : Affine.EvidenceProvider) : MetaM (Except Expr.Error Work) := do
  let mut work := work
  let mut firstError? := none
  for index in [:work.presentation.constraints.size] do
    let predicate := work.presentation.constraints[index]!.predicate
    if work.certifiedRows[index]!.isSome then continue
    let direct ← certifyPredicateDetailed predicate provider
    if let .ok rows := direct then
      work := { work with certifiedRows := work.certifiedRows.set! index (some rows) }
      continue
    let retained := splice (work.presentation.constraints.map (·.predicate)) index #[]
    match ← Morew.Elab.Conic.Rewrite.planUnique predicate retained provider with
    | .ok prepared =>
      let next ← applyPrepared work index prepared
      -- Every successful automatic plan certifies its generated rows. Therefore
      -- each restart removes one unresolved row and cannot create a cycle.
      return ← lower original next provider
    | .error error =>
      if firstError?.isNone then
        let error ← match direct with
          | .error directError => do
            let nativePSD ← lambdaTelescope predicate fun _ source => do
              let source ← Expr.reduceStructure source
              if source.isAppOf ``Matrix.PosSemidef then return true
              unless source.isAppOfArity ``Membership.mem 5 do return false
              let carrier ← Expr.reduceStructure source.getAppArgs[3]!
              unless carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1 do return false
              return (← Expr.reduceStructure carrier.getAppArgs[0]!).isAppOfArity
                ``Morew.Conic.Cone.positiveSemidefinite 1
            if nativePSD &&
                (← Registry.candidates .conic predicate).isEmpty then
              pure directError
            else pure error
          | .ok _ => pure error
        firstError? := some (← originalError original work.rowOrigins[index]! error)
  match firstError? with
  | some error => return .error error
  | none => return .ok work

-- Retain the accepted affine maps and their local evidence. Only their
-- equivalence endpoints change from the original leaves to membership leaves.
private def prepareNormalizations (domain source : Expr) (rows : Array RowResult) :
    MetaM (Array PredicateNormalization) := do
  let (leaves, _) ← decomposePredicate source
  unless leaves.size == rows.size do
    throwError "membership normalization does not match the certified row count"
  (rows.zip leaves).mapM fun (row, original) => do
    let conversion ← match row.normalization? with
      | some conversion => pure conversion
      | none => normalizePredicate original
    let expected ← withLocalDeclD `point domain fun point =>
      mkForallFVars #[point] (mkApp2 (mkConst ``Iff)
        (mkApp original point) (mkApp conversion.predicate point))
    if (← Morew.Elab.Rewrite.Plan.unresolved conversion.predicate) ||
        (← Morew.Elab.Rewrite.Plan.unresolved conversion.pointwiseIff) then
      throwError "cached membership normalization contains unresolved metavariables"
    unless ← isDefEq (← inferType conversion.pointwiseIff) expected do
      throwError "cached membership normalization does not match its source predicate"
    checkWithKernel conversion.pointwiseIff
    return conversion

private def transportRows (domain target : Expr) (rows : Array RowResult)
    (conversions : Array PredicateNormalization) :
    MetaM (Array RowResult) := do
  let (newLeaves, _) ← decomposePredicate target
  unless conversions.size == rows.size && newLeaves.size == rows.size do
    throwError "membership normalization changed the number of conic leaves"
  (rows.zip (conversions.zip newLeaves)).mapM fun (row, conversion, normalized) => do
    unless ← isDefEq conversion.predicate normalized do
      throwError "membership normalization changed the order of conic leaves"
    let pointwiseIff ← withLocalDeclD `point domain fun point => do
      mkLambdaFVars #[point] (← mkAppM ``Iff.trans
        #[mkApp row.pointwiseIff point, mkApp conversion.pointwiseIff point])
    checkWithKernel pointwiseIff
    return { row with pointwiseIff, normalization? := none }

/-- Normalize the actual final target and transport the already accepted row
certificates. Presentation-entry boundaries and provenance remain unchanged. -/
private def normalizeFinal (work : Work) : MetaM Work := do
  let mut work := work
  for index in [:work.presentation.constraints.size] do
    let source := work.presentation.constraints[index]!.predicate
    let some rows := work.certifiedRows[index]!
      | throwError "final membership normalization requires accepted conic rows"
    let conversions ← prepareNormalizations work.presentation.domainType source rows
    let normalized ← normalizePredicate source conversions
    unless normalized.changed do continue
    let presentation := work.presentation
    let retained := splice (presentation.constraints.map (·.predicate)) index #[]
    let conditional ← withLocalDeclD `point presentation.domainType fun point => do
      let remainder := Decomposition.conjunction (retained.toList.map (mkApp · point))
      withLocalDeclD `retained remainder fun hypothesis =>
        mkLambdaFVars #[point, hypothesis] (mkApp normalized.pointwiseIff point)
    let rewrite ← rewriteConstraintContextual presentation index
      #[normalized.predicate] conditional
    let rows ← transportRows presentation.domainType normalized.predicate rows conversions
    let constraints := presentation.constraints.modify index fun entry =>
      { entry with predicate := normalized.predicate }
    let presentation := { presentation with constraints }
    unless ← isDefEq (← presentation.canonicalProblem) rewrite.targetProblem do
      throwError "normalized conic presentation does not match its checked target"
    let equivalence ← instantiateMVars (← mkAppM ``Morew.GlobalEquivalence.trans
      #[work.equivalence, rewrite.equivalence])
    let origin := work.rowOrigins[index]!
    work := { work with
      presentation
      equivalence
      certifiedRows := work.certifiedRows.set! index (some rows)
      changedBodies := if work.changedBodies.contains origin then work.changedBodies
        else work.changedBodies.push origin
    }
  return work

/-- Plan an entire conic terminal step without allocating visible names or
emitting declarations. Failed attempts restore caller metavariables and the
environment. The first unresolved row is reported only after all later rows
have had an opportunity to supply a newly exposed retained margin. -/
def plan (presentation : PresentationState) (provider : Affine.EvidenceProvider := {}) :
    MetaM (Except Expr.Error Result) :=
  State.withIsolatedMVars do
    try
      for expression in #[presentation.domainType, presentation.valueType,
          presentation.objective] ++ presentation.constraints.map (·.predicate) do
        if ← Morew.Elab.Rewrite.Plan.unresolved expression then
          throwError "terminal conic planning requires fully elaborated expressions"
      Plan.withPresentationFiniteInstances
        (fun result oldVars newVars => result.replaceFVars oldVars newVars) presentation do
        match ← reifyObjective presentation provider with
        | .error error =>
          let bound := match presentation.sense with
            | .minimize => "epigraph t"
            | .maximize => "hypograph t"
          return .error { error with
            reason := ← addMessageContext m!"{error.reason}; use `{bound}` before `conic`" }
        | .ok _ => pure ()
        let canonical ← presentation.canonicalProblem
        let equivalence ← instantiateMVars (← mkAppM ``Morew.GlobalEquivalence.refl #[canonical])
        let work : Work := {
          presentation
          equivalence
          rowOrigins := presentation.constraints.mapIdx fun index _ => index
          certifiedRows := presentation.constraints.map fun _ => none
        }
        let work ← splitNonconicGroups work provider
        let work ← match ← lower presentation work provider with
          | .ok work => pure work
          | .error error => return .error error
        let work ← normalizeFinal work
        let form ← match ← buildForm work.presentation provider work.certifiedRows with
          | .ok form => pure form
          | .error error => return .error error
        checkWithKernel work.equivalence
        checkWithKernel form
        return .ok {
          presentation := work.presentation
          equivalence := work.equivalence
          form
          rowOrigins := work.rowOrigins
          replacedIndices := work.replacedIndices.qsort (· < ·)
          changedBodies := work.changedBodies.qsort (· < ·)
          auxiliaries := work.auxiliaries
        }
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext error.toMessageData
      }

end Morew.Elab.Conic.Terminal
