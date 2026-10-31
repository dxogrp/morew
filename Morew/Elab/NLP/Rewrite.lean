/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite
import Morew.Elab.Rewrite.Match
import Morew.Elab.NLP.Rules
import Morew.Elab.Rewrite.Plan
import Morew.Elab.NLP.Rows
import Morew.Elab.Expr
import Morew.Elab.State

/-!
# Exact replacement planning for selected nonlinear constraints

Registered rules match a complete selected predicate. Every candidate first supplies an
exact lift, possibly conditional on retained constraints, and then certifies its residuals on an
open domain containing the proposed feasible set. Retained predicates remain
unchanged, including predicates outside the generated-row grammar.

Automatic selection requires one fully certified registered rule. Explicit records
and declaration names bypass that search, but undergo the same exactness and
generated-row checks. Declaration names need not be registered.
No named arithmetic helper is unfolded and no affine certificate is required.
-/

namespace Morew.Elab.NLP.Rewrite

open Lean Lean.Meta

/-- Diagnostics identify the original selected predicate and the failed check. -/
abbrev Error := Expr.Error

/-- A checked exact replacement before presentation names are allocated. -/
structure Result extends Morew.Elab.Rewrite.Plan.Result where
  /-- Common-domain and smoothness evidence for precisely the generated rows. -/
  certified : Rows.Result

/-- Substitute scoped source evidence through every part of a completed plan. -/
def Result.replaceFVars (result : Result) (oldVars newVars : Array Expr) : Result :=
  { toResult := result.toResult.replaceFVars oldVars newVars
    certified := result.certified.replaceFVars oldVars newVars }

private abbrev conjunction := Morew.Elab.Rewrite.Decomposition.conjunction

-- Model fields are structural only when their named container is independent
-- of the decision point. Keep the same helper boundary as smooth certification.
-- Normalize nested structural forms before deciding that independence; retained
-- lets are opened by target decomposition so their evidence stays scoped.
private partial def structural (point expression : Expr) (preserveLets : Bool := false) :
    MetaM Expr := do
  let step (value : Expr) : MetaM TransformStep := do
    let reduced ← Expr.reduceStructure value (preserveLets := preserveLets)
      (opaqueProblemDependencies? := some point)
    let reduced := if reduced.isAppOf ``Function.comp && reduced.getAppNumArgs ≥ 6 then
        let args := reduced.getAppArgs
        mkAppN (mkApp args[3]! (mkApp args[4]! args[5]!)) (args.extract 6 args.size)
      else reduced
    if let .letE name type binding body nondep := reduced then
      if preserveLets && !(← Expr.depends point type) &&
          !(← Expr.depends point binding) then
        return ← withLetDecl name type binding (nondep := nondep) fun bindingVar => do
          let body ← structural point (body.instantiate1 bindingVar) preserveLets
          return .done (← mkLetFVars #[bindingVar] body
            (usedLetOnly := false) (generalizeNondepLet := false))
      return .visit (body.instantiate1 binding)
    if reduced != value then return .visit reduced
    if !(← Expr.depends point value) then return .done value
    return .continue
  Meta.transform expression (pre := step) (post := step)

-- Expose representation fields, not arbitrary target predicate definitions.
private partial def exposeTarget (point body : Expr) : MetaM Expr := do
  let body ← structural point body (preserveLets := true)
  let head := body.getAppFn
  let prefixSize? := match head.constName? with
    | some ``Morew.ExactConstraintLift.target => some 3
    | some ``Morew.GraphRepresentation.target => some 4
    | some ``Morew.EpigraphRepresentation.target => some 5
    | some ``Morew.HypographRepresentation.target => some 5
    | _ => none
  if let some prefixSize := prefixSize? then
    let args := body.getAppArgs
    if args.size >= prefixSize then
      -- Normalize only the record container. Normalizing the whole projection
      -- would also unfold a named predicate stored in its target field.
      let record ← whnf args[prefixSize - 1]!
      if let some field ← projectCore? record 1 then
        return ← exposeTarget point (mkAppN field (args.extract prefixSize args.size))
  return body

-- Native rules expose a bound's operands and can thereby discard unused source
-- evidence. Keep independent proof lets in each emitted predicate as well as in
-- its current certificate, so later reformulations can certify it again.
private partial def retainSourceEvidence (point source body : Expr) : MetaM Expr := do
  let source ← structural point source (preserveLets := true)
  if let .letE name type value rest nondep := source then
    if !(← isProp type) then
      return ← retainSourceEvidence point (rest.instantiate1 value) body
    withLetDecl name type value (nondep := nondep) fun binding => do
      let body ← retainSourceEvidence point (rest.instantiate1 binding) body
      mkLetFVars #[binding] body (usedLetOnly := false) (generalizeNondepLet := false)
  else return body

private def finish (source domain : Expr) (certificate : Morew.Elab.Rewrite.Plan.Certificate)
    (retained : Array Expr)
    (insertionIndex : Nat) : MetaM Result := do
  -- Exactness is checked before any generated constraint can supply evidence.
  certificate.check source retained
  unless ← Domain.Evidence.complete certificate.expression do
    throwError "the exact certificate contains unresolved placeholders"
  let auxiliary ← whnf (← certificate.auxiliaryType)
  let noAuxiliary ← isDefEq auxiliary (mkConst ``Unit)
  let auxiliary? := if noAuxiliary then none else some auxiliary
  let nextDomain ← if noAuxiliary then pure domain else mkAppM ``Prod #[domain, auxiliary]
  discard <| Space.withCanonicalSpaces #[nextDomain] (pure (mkConst ``True.intro))
  let targetFunction ← certificate.targetFunction
  let (rowPredicates, targetIff, feasible) ← withLocalDeclD `point nextDomain fun point => do
    let original := if noAuxiliary then point else .proj ``Prod 0 point
    let auxiliary := if noAuxiliary then mkConst ``Unit.unit else .proj ``Prod 1 point
    let target := mkApp2 targetFunction original auxiliary
    let (bodies, proof) ← Morew.Elab.Rewrite.Decomposition.split target (exposeTarget point)
    let bodies ← bodies.mapM (retainSourceEvidence point (mkApp source original))
    let rows ← bodies.toArray.mapM (mkLambdaFVars #[point])
    let targetIff ← mkLambdaFVars #[point] proof
    let retainedBodies := retained.map (mkApp · original)
    let allBodies := retainedBodies.extract 0 insertionIndex ++ bodies.toArray ++
      retainedBodies.extract insertionIndex retainedBodies.size
    let feasible ← mkLambdaFVars #[point] (conjunction allBodies.toList)
    return (rows, targetIff, feasible)
  let prepared : Morew.Elab.Rewrite.Plan.Result := {
    certificate, auxiliary?, nextDomain, rowPredicates, targetIff }
  prepared.checkTargetIff "internal error: target decomposition changed the exact lift"
  let certified ← match ← Rows.certifyRows feasible rowPredicates with
    | .ok certified => pure certified
    | .error error => throwError "generated row certification failed: {error.reason}"
  return { toResult := prepared, certified }

private def proveObligation (point evidence obligation : Expr) : MetaM (Option Expr) := do
  let facts ← Rows.factsProvider point evidence obligation
  if let some proof ← Domain.Evidence.prove? point obligation facts then return some proof
  throwError "registered NLP rewrite was not certified: missing retained premise {obligation}"

private def matchAndFinish (source domain : Expr) (retained : Array Expr)
    (matchRule : Expr → Expr → Morew.Elab.Rewrite.Match.Prove →
      (Morew.Elab.Rewrite.Match.Result → MetaM Result) → MetaM Result)
    (finishCertificate : Morew.Elab.Rewrite.Plan.Certificate → MetaM Result) : MetaM Result :=
  withLocalDeclD `point domain fun point => do
    let body ← structural point (mkApp source point)
    let remainder := conjunction (retained.toList.map (mkApp · point))
    withLocalDecl `retained .default remainder (kind := .implDetail) fun evidence => do
      matchRule point body (proveObligation point evidence) fun matched => do
        let auxiliary ← whnf (← instantiateMVars matched.auxiliary)
        let target ← withLocalDeclD `auxiliary auxiliary fun auxiliary => do
          mkLambdaFVars #[auxiliary] (← exposeTarget point (mkApp matched.target auxiliary))
        let certificate ← Morew.Elab.Rewrite.Plan.closeCertificate source point evidence
          auxiliary target matched.sourceIff
        finishCertificate certificate

private def registeredCandidates (source domain : Expr) : MetaM (Array Name) :=
  withLocalDeclD `point domain fun point => do
    let body ← structural point (mkApp source point)
    let predicate ← mkLambdaFVars #[point] body
    Morew.Elab.Rewrite.Registry.candidates .nlp predicate

private def failure (source : Expr) (exception : Exception) : MetaM Error := do
  return { expression := source, reason := ← addMessageContext exception.toMessageData }

private def planCore (source : Expr) (retained : Array Expr)
    (rule? : Option Expr) (insertionIndex : Nat) (declaration? : Option Name) :
    MetaM (Except Error Result) := do
  try
    unless insertionIndex ≤ retained.size do
      throwError "constraint replacement insertion index is out of bounds"
    let source ← instantiateMVars source
    for expression in #[source] ++ retained ++ rule?.toArray do
      unless ← Domain.Evidence.complete expression do
        throwError "unresolved metavariables or placeholders in the exact replacement input"
    let domain ← Morew.Elab.Rewrite.Plan.predicateDomain source
    discard <| Space.withCanonicalSpaces #[domain] (pure (mkConst ``True.intro))
    for row in retained do
      unless ← isDefEq (← inferType row) (← mkArrow domain (mkSort .zero)) do
        throwError "a retained row has a different decision space"
    let finishCertificate := fun certificate => finish source domain certificate retained insertionIndex
    let finishDeclaration := fun name accept => matchAndFinish source domain retained
      (fun point body prove accept => Morew.Elab.Rewrite.Match.declaration point body name accept prove) accept
    if let some name := declaration? then
      return .ok (← finishDeclaration name finishCertificate)
    if let some rule := rule? then
      -- Concrete graph and bound records use the same typed matcher as named
      -- registrations. Definitional equality alone could erase a custom source
      -- operation before its actual instance has been checked.
      unless (← whnf (← inferType rule)).isAppOfArity ``Morew.ExactConstraintLift 2 do
        return .ok (← matchAndFinish source domain retained
          (fun point body prove accept =>
            Morew.Elab.Rewrite.Match.rule point body rule accept prove) finishCertificate)
      let direct : Except Exception Result ← State.withIsolatedMVars do
        try return .ok (← finishCertificate
          (.exact (← Morew.Elab.Rewrite.Plan.checkLift source rule)))
        catch exception => return .error exception
      match direct with
      | .ok result => return .ok result
      | .error original =>
        -- A supplied exact lift retains its whole-input interpretation; the
        -- checked retry can discharge subtype guards from retained evidence.
        let reachedTarget ← IO.mkRef false
        let reachedPremise ← IO.mkRef false
        try
          return .ok (← matchAndFinish source domain retained
            (fun point body prove accept =>
              Morew.Elab.Rewrite.Match.rule point body rule accept fun obligation => do
                reachedPremise.set true
                prove obligation)
            (fun certificate => do
              reachedTarget.set true
              finishCertificate certificate))
        catch error =>
          if (← reachedTarget.get) || (← reachedPremise.get) then throw error
          throw original
    let mut successes : Array (Name × Result) := #[]
    let mut firstMatchError? := none
    let mut firstError? := none
    for selected in ← registeredCandidates source domain do
      let reachedTarget ← IO.mkRef false
      let attempt : Except (Bool × Error) Result ← State.withIsolatedMVars do
        try
          return .ok (← finishDeclaration selected fun certificate => do
            reachedTarget.set true
            finishCertificate certificate)
        catch exception => return .error (← reachedTarget.get, ← failure source exception)
      match attempt with
      | .ok result => successes := successes.push (selected, result)
      | .error (true, error) => if firstError?.isNone then firstError? := some error
      | .error (false, error) =>
        if firstMatchError?.isNone then firstMatchError? := some error
    if let [(_, result)] := successes.toList then return .ok result
    if successes.size > 1 then
      let names := successes.toList.map (fun (name, _) => name.toString)
      throwError "ambiguous exact NLP rules: {String.intercalate ", " names}; select one with `using ruleName`"
    if let some error := firstError? then return .error error
    let detail := firstMatchError?.map (fun error => m!"\ncandidate matching: {error.reason}")
      |>.getD m!""
    throwError "no supported exact NLP rule for the entire selected predicate; no registered certificate matches; register an exact representation or use an explicit exact record\nselected predicate: {source}\npredicate type: {← inferType source}{detail}"
  catch exception => return .error (← failure source exception)

/-- Plan one complete selected predicate. The retained rows are in their original
order with the selected row removed; generated rows are inserted at `insertionIndex`.
Only supplied records/declarations or registered whole-predicate rules are tried. Failed attempts and
ambiguous selection restore caller metavariables and environment declarations. -/
def plan (source : Expr) (retained : Array Expr) (rule? : Option Expr := none)
    (insertionIndex : Nat := 0) (declaration? : Option Name := none) :
    MetaM (Except Error Result) :=
  State.withIsolatedMVars do
    try
      let mut instances := #[]
      for expression in #[source] ++ retained ++ rule?.toArray do
        for inst in ← Expr.sourceFiniteInstances expression do
          unless instances.contains inst do instances := instances.push inst
      Morew.Elab.Rewrite.Plan.withScopedFiniteInstances
        (fun result oldVars newVars => result.map (·.replaceFVars oldVars newVars))
        instances.toList do
          let domain ← Morew.Elab.Rewrite.Plan.predicateDomain source
          withLocalDeclD `point domain fun point =>
            Morew.Elab.Rewrite.Plan.withScopedEvidence
              (fun result oldVars newVars => result.map (·.replaceFVars oldVars newVars))
              point (mkApp source point) (planCore source retained rule? insertionIndex declaration?)
    catch exception => return .error (← failure source exception)

end Morew.Elab.NLP.Rewrite
