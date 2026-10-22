import PTran.Elab.Conic.Automatic
import PTran.Elab.Conic.Decomposition
import PTran.Elab.Conic.Form
import PTran.Elab.Conic.Rewrite

/-!
# Whole-problem exact conic planning

Plan all row rewrites before allocating surface names. Already-conic named
groups retain their boundaries; groups containing unsupported leaves are split
exactly so their affine siblings can supply retained domain evidence.
-/

namespace PTran.Elab.Conic.Terminal

open Lean Lean.Meta
open PTran.Elab.Reformulation

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
  replacedIndices : Array Nat := #[]
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

private def isConicPredicate (predicate : Expr) (config : Affine.Config) : MetaM Bool := do
  let (leaves, _) ← decomposePredicate predicate
  for leaf in leaves do
    if let .error _ ← normalizeRow leaf config then return false
  return true

/-- Apply the same domain pullback as the checked rewrite and retain original
entry provenance independently of the temporary presentation names. -/
private def applyReplacement (work : Work) (index : Nat) (rows : Array Expr)
    (nextDomain : Expr) (auxiliary? : Option Expr) (rewrite : RewriteResult) : MetaM Work := do
  let origin := work.rowOrigins[index]!
  let old := work.presentation
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
    old with
    domainType := nextDomain
    binders
    objective
    constraints := splice retained index entries
  }
  let canonical ← presentation.canonicalProblem
  unless ← isDefEq canonical rewrite.targetProblem do
    throwError "terminal rewrite presentation does not match its checked target"
  let equivalence ← instantiateMVars (← mkAppM ``PTran.GlobalEquivalence.trans
    #[work.equivalence, rewrite.equivalence])
  let replacedIndices := if work.replacedIndices.contains origin then work.replacedIndices
    else work.replacedIndices.push origin
  return {
    presentation
    equivalence
    rowOrigins := splice work.rowOrigins index (rows.map fun _ => origin)
    replacedIndices
    auxiliaries
    nextName
  }

/-- Split all nonlinear groups before searching for exact rewrites. This makes
affine domain margins in the same original group available to sibling leaves. -/
private def splitNonconicGroups (work : Work) (config : Affine.Config) : MetaM Work := do
  let mut work := work
  let mut index := 0
  while index < work.presentation.constraints.size do
    let source := work.presentation.constraints[index]!.predicate
    let (leaves, decomposition) ← decomposePredicate source
    if ← isConicPredicate source config then
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
    work ← applyReplacement work index leaves presentation.domainType none rewrite
    index := index + leaves.size
  return work

private def applyPrepared (work : Work) (index : Nat) (prepared : Plan.Prepared) : MetaM Work := do
  match prepared with
  | .inl exact =>
    let rewrite ← rewriteConstraint work.presentation index exact.lift exact.auxiliary?
      exact.nextDomain exact.rowPredicates exact.targetIff
    applyReplacement work index exact.rowPredicates exact.nextDomain exact.auxiliary? rewrite
  | .inr contextual =>
    let rewrite ← rewriteConstraintContextual work.presentation index
      contextual.rowPredicates contextual.conditionalIff
    applyReplacement work index contextual.rowPredicates contextual.domain none rewrite

private def originalError (original : PresentationState) (origin : Nat)
    (error : Affine.AffineError) : MetaM Affine.AffineError := do
  let label := original.constraints[origin]!.name.eraseMacroScopes
  let reason ← addMessageContext
    m!"constraint `{label}`: {error.reason}\nunsupported expression: {error.expression}\nuse `conic at {label} using rule` with an exact representation before `conic`"
  return { error with reason }

private partial def lower (original : PresentationState) (work : Work)
    (config : Affine.Config) : MetaM (Except Affine.AffineError Work) := do
  let mut firstError? := none
  for index in [:work.presentation.constraints.size] do
    let predicate := work.presentation.constraints[index]!.predicate
    if ← isConicPredicate predicate config then continue
    let retained := splice (work.presentation.constraints.map (·.predicate)) index #[]
    match ← Automatic.planUnique predicate retained config with
    | .ok prepared =>
      let next ← applyPrepared work index prepared
      -- Every successful automatic plan certifies its generated rows. Therefore
      -- each restart removes one unresolved row and cannot create a cycle.
      return ← lower original next config
    | .error error =>
      if firstError?.isNone then
        firstError? := some (← originalError original work.rowOrigins[index]! error)
  match firstError? with
  | some error => return .error error
  | none => return .ok work

/-- Plan an entire conic terminal step without allocating visible names or
emitting declarations. Failed attempts restore caller metavariables and the
environment. The first unresolved row is reported only after all later rows
have had an opportunity to supply a newly exposed retained margin. -/
def plan (presentation : PresentationState) (config : Affine.Config := {}) :
    MetaM (Except Affine.AffineError Result) :=
  Affine.withIsolatedMVars do
    try
      for expression in #[presentation.domainType, presentation.valueType,
          presentation.objective] ++ presentation.constraints.map (·.predicate) do
        if ← Plan.unresolved expression then
          throwError "terminal conic planning requires fully elaborated expressions"
      match ← reifyObjective presentation config with
      | .error error =>
        let bound := match presentation.sense with
          | .minimize => "epigraph t"
          | .maximize => "hypograph t"
        return .error { error with
          reason := ← addMessageContext m!"{error.reason}; use `{bound}` before `conic`" }
      | .ok _ => pure ()
      let canonical ← presentation.canonicalProblem
      let equivalence ← instantiateMVars (← mkAppM ``PTran.GlobalEquivalence.refl #[canonical])
      let work : Work := {
        presentation
        equivalence
        rowOrigins := presentation.constraints.mapIdx fun index _ => index
      }
      let work ← splitNonconicGroups work config
      let work ← match ← lower presentation work config with
        | .ok work => pure work
        | .error error => return .error error
      let form ← match ← buildForm work.presentation config with
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
        auxiliaries := work.auxiliaries
      }
    catch error =>
      return .error {
        expression := presentation.objective
        reason := ← addMessageContext error.toMessageData
      }

end PTran.Elab.Conic.Terminal
