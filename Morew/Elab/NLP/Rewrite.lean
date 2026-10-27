/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite
import Morew.Elab.Rewrite.Match
import Morew.Elab.NLP.Rules
import Morew.Elab.Rewrite.Plan
import Morew.Elab.NLP.Rows

/-!
# Exact replacement planning for selected nonlinear constraints

Registered rules match a complete selected predicate. Every candidate first supplies an
unconditional exact lift and then certifies only its generated residuals on an
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
abbrev Error := Affine.AffineError

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
    let reduced ← Affine.reduceStructure value (preserveLets := preserveLets)
      (opaqueProblemDependencies? := some point)
    let reduced := if reduced.isAppOf ``Function.comp && reduced.getAppNumArgs ≥ 6 then
        let args := reduced.getAppArgs
        mkAppN (mkApp args[3]! (mkApp args[4]! args[5]!)) (args.extract 6 args.size)
      else reduced
    if let .letE name type binding body nondep := reduced then
      if preserveLets && !(← Affine.depends point type) &&
          !(← Affine.depends point binding) then
        return ← withLetDecl name type binding (nondep := nondep) fun bindingVar => do
          let body ← structural point (body.instantiate1 bindingVar) preserveLets
          return .done (← mkLetFVars #[bindingVar] body
            (usedLetOnly := false) (generalizeNondepLet := false))
      return .visit (body.instantiate1 binding)
    if reduced != value then return .visit reduced
    if !(← Affine.depends point value) then return .done value
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

private def finish (source domain lift : Expr) (retained : Array Expr)
    (insertionIndex : Nat) : MetaM Result := do
  -- Exactness is checked before any generated constraint can supply evidence.
  let lift ← Morew.Elab.Rewrite.Plan.checkLift source lift
  unless ← Domain.Evidence.complete lift do
    throwError "the exact certificate contains unresolved placeholders"
  let auxiliary ← whnf (← mkAppM ``Morew.ExactConstraintLift.Auxiliary #[lift])
  let noAuxiliary ← isDefEq auxiliary (mkConst ``Unit)
  let auxiliary? := if noAuxiliary then none else some auxiliary
  let nextDomain ← if noAuxiliary then pure domain else mkAppM ``Prod #[domain, auxiliary]
  discard <| Space.withCanonicalSpaces #[nextDomain] (pure (mkConst ``True.intro))
  let targetFunction ← mkAppM ``Morew.ExactConstraintLift.target #[lift]
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
    lift, auxiliary?, nextDomain, rowPredicates, targetIff }
  prepared.checkTargetIff "internal error: target decomposition changed the exact lift"
  let certified ← match ← Rows.certifyRows feasible rowPredicates with
    | .ok certified => pure certified
    | .error error => throwError "generated row certification failed: {error.reason}"
  return { toResult := prepared, certified }

private def matchAndFinish (source domain : Expr)
    (matchRule : Expr → Expr →
      (Morew.Elab.Rewrite.Match.Result → MetaM Result) → MetaM Result)
    (finishLift : Expr → MetaM Result) : MetaM Result :=
  withLocalDeclD `point domain fun point => do
    let body ← structural point (mkApp source point)
    -- No retained-evidence callback is supplied to either matcher. Exactness
    -- remains unconditional; only the finished rows use feasibility evidence.
    matchRule point body fun matched => do
      if ← Affine.depends point matched.auxiliary then
        throwError "the auxiliary space depends on a decision variable"
      let target ← mkLambdaFVars #[point] matched.target
      let pointwise ← mkLambdaFVars #[point] matched.sourceIff
      let lift ← instantiateMVars (← mkAppM ``Morew.ExactConstraintLift.mk
        #[matched.auxiliary, target, pointwise])
      finishLift lift

private def registeredCandidates (source domain : Expr) : MetaM (Array Name) :=
  withLocalDeclD `point domain fun point => do
    let body ← structural point (mkApp source point)
    let predicate ← mkLambdaFVars #[point] body
    Morew.Elab.Rewrite.Registry.candidates .nlp predicate

private def proofSides (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Iff 2 do throwError "internal error: expected exact iff evidence"
  return (type.getAppArgs[0]!, type.getAppArgs[1]!)

-- Higher-order unification cannot always recover a pair from separate field
-- constraints, notably `using maxEpigraph` on a constant bound. Expose only
-- product constructors in these fresh inference patterns; source expressions
-- and the supplied representation remain unchanged.
private partial def freshInput (type : Expr) : MetaM Expr := do
  let shape ← whnf type
  if shape.isAppOfArity ``Prod 2 then
    mkAppM ``Prod.mk #[← freshInput shape.getAppArgs[0]!,
      ← freshInput shape.getAppArgs[1]!]
  else mkFreshExprMVar type

private def adaptProductRepresentation (source domain rule : Expr)
    (inputType outputType : Expr) (proofName adapter : Name)
    (symmetric : Bool := false) : MetaM Expr :=
  withLocalDeclD `point domain fun point => do
    let input ← freshInput inputType
    let output ← freshInput outputType
    let proof ← mkAppM proofName #[rule, input, output]
    let (predicate, _) ← proofSides proof
    let predicate ← if symmetric then
        mkEq predicate.getAppArgs[2]! predicate.getAppArgs[1]!
      else pure predicate
    unless ← isDefEq predicate (mkApp source point) do
      throwError "the supplied exact certificate does not describe the entire selected predicate"
    let input ← instantiateMVars input
    let output ← instantiateMVars output
    unless (← Domain.Evidence.complete input) && (← Domain.Evidence.complete output) do
      throwError "cannot infer the exact representation's input and bound maps; supply an explicitly instantiated ExactConstraintLift"
    let input ← mkLambdaFVars #[point] input
    let output ← mkLambdaFVars #[point] output
    Morew.Elab.Rewrite.Plan.checkLift source (← mkAppM adapter #[rule, input, output])

private def customLift (source domain rule : Expr) : MetaM Expr := do
  let saved ← saveState
  try
    return ← Morew.Elab.Rewrite.Plan.customLift source domain rule
  catch original =>
    saved.restore
    let type ← whnf (← inferType rule)
    let args := type.getAppArgs
    if type.isAppOfArity ``Morew.EpigraphRepresentation 4 then
      return ← adaptProductRepresentation source domain rule args[0]! args[1]!
        ``Morew.EpigraphRepresentation.source_iff_exists
        ``Morew.EpigraphRepresentation.toExactConstraintLift
    if type.isAppOfArity ``Morew.HypographRepresentation 4 then
      return ← adaptProductRepresentation source domain rule args[0]! args[1]!
        ``Morew.HypographRepresentation.source_iff_exists
        ``Morew.HypographRepresentation.toExactConstraintLift
    if type.isAppOfArity ``Morew.GraphRepresentation 3 then
      let saved ← saveState
      try
        return ← adaptProductRepresentation source domain rule args[0]! args[1]!
          ``Morew.GraphRepresentation.source_iff_exists
          ``Morew.GraphRepresentation.toExactConstraintLift
      catch _ =>
        saved.restore
        return ← adaptProductRepresentation source domain rule args[0]! args[1]!
          ``Morew.GraphRepresentation.source_iff_exists
          ``Morew.GraphRepresentation.toExactConstraintLiftSymm true
    throw original

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
    let finishLift := fun lift => finish source domain lift retained insertionIndex
    let finishDeclaration := fun name accept => matchAndFinish source domain
      (fun point body => Morew.Elab.Rewrite.Match.declaration point body name) accept
    if let some name := declaration? then
      return .ok (← finishDeclaration name finishLift)
    if let some rule := rule? then
      let direct : Except Exception Result ← Affine.withIsolatedMVars do
        try return .ok (← finishLift (← customLift source domain rule))
        catch exception => return .error exception
      match direct with
      | .ok result => return .ok result
      | .error original =>
        -- Keep the existing concrete-record adapters, including exact lifts'
        -- full-source check. Only graph orientation needs a certified retry.
        unless (← whnf (← inferType rule)).isAppOfArity ``Morew.GraphRepresentation 3 do
          throw original
        try
          return .ok (← matchAndFinish source domain
            (fun point body => Morew.Elab.Rewrite.Match.rule point body rule) finishLift)
        catch _ => throw original
    let mut successes : Array (Name × Result) := #[]
    let mut firstMatchError? := none
    let mut firstError? := none
    for selected in ← registeredCandidates source domain do
      let reachedTarget ← IO.mkRef false
      let attempt : Except (Bool × Error) Result ← Affine.withIsolatedMVars do
        try
          return .ok (← finishDeclaration selected fun lift => do
            reachedTarget.set true
            finishLift lift)
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
  Affine.withIsolatedMVars do
    try
      let mut instances := #[]
      for expression in #[source] ++ retained ++ rule?.toArray do
        for inst in ← Affine.sourceFiniteInstances expression do
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
