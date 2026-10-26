/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Rewrite
import Morew.Elab.Atom
import Morew.Elab.Rewrite.Plan
import Morew.Elab.NLP.Rows

/-!
# Exact replacement planning for selected nonlinear constraints

Native rules match a complete scalar bound. Every candidate first supplies an
unconditional exact lift and then certifies only its generated residuals on an
open domain containing the proposed feasible set. Retained predicates remain
unchanged, including predicates outside the generated-row grammar.

Automatic selection requires one fully certified native rule. Explicit records
bypass that search, but undergo the same exactness and generated-row checks.
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

-- Referenced local values and types can hide placeholders from `Expr.hasSorry`.
private partial def incomplete (expression : Expr) (seen : FVarIdSet := {}) :
    MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasMVar || expression.hasSorry then return true
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    unless seen.contains id do
      seen := seen.insert id
      if let some declaration := (← getLCtx).find? id then
        if ← incomplete declaration.type seen then return true
        if let some value := declaration.value? (allowNondep := true) then
          if ← incomplete value seen then return true
  return false

private def finish (source domain lift : Expr) (retained : Array Expr)
    (insertionIndex : Nat) : MetaM Result := do
  -- Exactness is checked before any generated constraint can supply evidence.
  let lift ← Morew.Elab.Rewrite.Plan.checkLift source lift
  if ← incomplete lift then throwError "the exact certificate contains unresolved placeholders"
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

private inductive Rule where
  | absolute | positivePart | maximum | minimum | supremum | infimum
  | normOne | normInfinity | normTwo
  deriving BEq

private def Rule.name : Rule → Name
  | .absolute => ``Morew.Rewrite.absEpigraph
  | .positivePart => ``Morew.Rewrite.posEpigraph
  | .maximum => ``Morew.Rewrite.maxEpigraph
  | .minimum => ``Morew.Rewrite.minHypograph
  | .supremum => ``Morew.Rewrite.finsetSupEpigraph
  | .infimum => ``Morew.Rewrite.finsetInfHypograph
  | .normOne => ``Morew.Rewrite.norm1Epigraph
  | .normInfinity => ``Morew.Rewrite.normInfEpigraph
  | .normTwo => ``Morew.Rewrite.norm2Epigraph

private def rules : Array Rule := #[.absolute, .positivePart, .maximum, .minimum,
  .supremum, .infimum, .normOne, .normInfinity, .normTwo]

private def realVectorDimension? (type : Expr) : MetaM (Option Expr) := do
  let .forallE _ index body _ ← whnf type | return none
  let index ← whnf index
  unless index.isAppOfArity ``Fin 1 do return none
  withLocalDeclD `i index fun i => do
    let body ← Core.betaReduce (← whnf (body.instantiate1 i))
    unless body.isConstOf ``Real do return none
    return some index.getAppArgs[0]!

-- Compare instances themselves, even when an altered instance happens to
-- coincide with the native operation on these particular operands.
private def sameOperationPrefix (actual expected : Expr) (operandCount : Nat) :
    MetaM Unit := do
  unless actual.getAppFn == expected.getAppFn &&
      actual.getAppNumArgs == expected.getAppNumArgs do
    throwError "unsupported native operation {actual}"
  let a := actual.getAppArgs
  let b := expected.getAppArgs
  for index in [:a.size - operandCount] do
    unless ← isDefEq a[index]! b[index]! do
      throwError "unsupported instance in native operation {actual}"

private def representationProof (rule input bound : Expr) (hypograph : Bool := false) :
    MetaM Expr :=
  mkAppM (if hypograph then ``Morew.HypographRepresentation.source_iff_exists
    else ``Morew.EpigraphRepresentation.source_iff_exists) #[rule, input, bound]

private def proofSides (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Iff 2 do throwError "internal error: expected exact iff evidence"
  return (type.getAppArgs[0]!, type.getAppArgs[1]!)

private def normProof? (selected : Rule) (point operation bound : Expr) :
    MetaM (Option (Name × Expr)) := do
  unless operation.isAppOfArity ``Norm.norm 3 do return none
  let vector := operation.getAppArgs[2]!
  let vectorType ← inferType vector
  let proof? ← if let some n ← realVectorDimension? vectorType then do
      if selected != .normInfinity then return none
      pure <| some (``Morew.Rewrite.normInfEpigraph, ← representationProof
        (← mkAppOptM ``Morew.Rewrite.normInfEpigraph #[some n]) vector bound)
    else do
      let reduced ← structural point vector
      if reduced.isAppOfArity ``WithLp.toLp 3 then
        let raw := reduced.getAppArgs[2]!
        let some n ← realVectorDimension? (← inferType raw) | return none
        let name := if selected == .normOne then ``Morew.Rewrite.norm1Epigraph
          else if selected == .normInfinity then ``Morew.Rewrite.normInfToLpEpigraph
          else ``Morew.Rewrite.norm2Epigraph
        let proof ← representationProof (← mkAppOptM name #[some n]) raw bound
        let (source, _) ← proofSides proof
        let source ← structural point source
        let expected ← structural point source.getAppArgs[2]!
        unless ← isDefEq vector expected.getAppArgs[2]! do return none
        pure (some (name, proof))
      else if let some n ← Affine.Space.euclideanDimension? vectorType then
        if selected != .normTwo then return none
        pure <| some (``Morew.Rewrite.euclideanNormEpigraph, ← representationProof
          (← mkAppOptM ``Morew.Rewrite.euclideanNormEpigraph #[some n]) vector bound)
      else pure none
  let some (name, proof) := proof? | return none
  let (source, _) ← proofSides proof
  let source ← structural point source
  sameOperationPrefix operation (← structural point source.getAppArgs[2]!) 1
  return some (name, proof)

private def nativeProof? (selected : Rule) (point body : Expr) :
    MetaM (Option (Name × Expr)) := do
  let body ← structural point body
  let greaterEqual := body.isAppOfArity ``GE.ge 4
  unless greaterEqual || body.isAppOfArity ``LE.le 4 do return none
  let args := body.getAppArgs
  unless ← isDefEq args[0]! (mkConst ``Real) do return none
  unless ← isDefEq args[1]! (mkConst ``Real.instLE) do
    throwError "unsupported order instance in the selected predicate"
  let left ← structural point args[if greaterEqual then 3 else 2]!
  let right ← structural point args[if greaterEqual then 2 else 3]!
  if let some operation ← Atom.recognizeAtom? left then
    let operands := operation.operands
    if (selected == .absolute && operation.kind == .abs) ||
        (selected == .positivePart && operation.kind == .pos) then
      return some (selected.name, ← representationProof (mkConst selected.name) operands[0]! right)
    if selected == .maximum && operation.kind == .maximum then
      let input ← mkAppM ``Prod.mk #[operands[0]!, operands[1]!]
      return some (selected.name, ← representationProof (mkConst selected.name) input right)
  if selected == .minimum then
    if let some operation ← Atom.recognizeAtom? right then
      if operation.kind == .minimum then
        let input ← mkAppM ``Prod.mk #[operation.operands[0]!, operation.operands[1]!]
        return some (selected.name, ← representationProof (mkConst selected.name) input left true)
  if (selected == .supremum && left.isAppOfArity ``Finset.sup' 6) ||
      (selected == .infimum && right.isAppOfArity ``Finset.inf' 6) then
    let minimum := selected == .infimum
    let operation := if minimum then right else left
    let args := operation.getAppArgs
    if ← Affine.depends point args[3]! then
      throwError "the finite extremum's index set depends on a decision variable"
    let rule ← mkAppM selected.name #[args[3]!, args[4]!]
    let proof ← representationProof rule args[5]! (if minimum then left else right) minimum
    let (source, _) ← proofSides proof
    let source ← structural point source
    sameOperationPrefix operation
      (← structural point source.getAppArgs[if minimum then 3 else 2]!) 3
    return some (selected.name, proof)
  if selected == .normOne || selected == .normInfinity || selected == .normTwo then
    return ← normProof? selected point left right
  return none

private def automaticLift? (selected : Rule) (source domain : Expr) :
    MetaM (Option (Name × Expr)) :=
  withLocalDeclD `point domain fun point => do
    let body ← structural point (mkApp source point)
    let some (name, proof) ← nativeProof? selected point body | return none
    let (provedSource, target) ← proofSides proof
    unless ← isDefEq provedSource body do
      throwError "the native exact rule does not describe the entire selected predicate"
    unless target.isAppOfArity ``Exists 2 do
      throwError "internal error: native representation omitted its existential target"
    let args := target.getAppArgs
    let auxiliary ← whnf args[0]!
    if ← Affine.depends point auxiliary then
      throwError "the auxiliary space depends on a decision variable"
    let target ← mkLambdaFVars #[point] args[1]!
    let pointwise ← mkLambdaFVars #[point] proof
    return some (name, ← instantiateMVars (← mkAppM ``Morew.ExactConstraintLift.mk
      #[auxiliary, target, pointwise]))

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
    if (← incomplete input) || (← incomplete output) then
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
    (rule? : Option Expr) (insertionIndex : Nat) : MetaM (Except Error Result) := do
  try
    unless insertionIndex ≤ retained.size do
      throwError "constraint replacement insertion index is out of bounds"
    let source ← instantiateMVars source
    for expression in #[source] ++ retained ++ rule?.toArray do
      if ← incomplete expression then
        throwError "unresolved metavariables or placeholders in the exact replacement input"
    let domain ← Morew.Elab.Rewrite.Plan.predicateDomain source
    discard <| Space.withCanonicalSpaces #[domain] (pure (mkConst ``True.intro))
    for row in retained do
      unless ← isDefEq (← inferType row) (← mkArrow domain (mkSort .zero)) do
        throwError "a retained row has a different decision space"
    let finishLift := fun lift => finish source domain lift retained insertionIndex
    if let some rule := rule? then
      return .ok (← finishLift (← customLift source domain rule))
    let mut successes : Array (Name × Result) := #[]
    let mut firstError? := none
    for selected in rules do
      let attempt : Except Error (Option (Name × Result)) ← Affine.withIsolatedMVars do
        try
          let some (name, lift) ← automaticLift? selected source domain | return .ok none
          return .ok (some (name, ← finishLift lift))
        catch exception => return .error (← failure source exception)
      match attempt with
      | .ok (some result) => successes := successes.push result
      | .ok none => pure ()
      | .error error => if firstError?.isNone then firstError? := some error
    if let [(_, result)] := successes.toList then return .ok result
    if successes.size > 1 then
      let names := successes.toList.map (fun (name, _) => name.toString)
      throwError "ambiguous exact NLP rules: {String.intercalate ", " names}; select one with `using ruleName`"
    if let some error := firstError? then return .error error
    throwError "no supported exact NLP rule for the entire selected predicate; expected an absolute-value, positive-part, maximum, finite-supremum, or supported norm upper bound, or a minimum/finite-infimum lower bound; use an explicit exact record for other predicates\nselected predicate: {source}\npredicate type: {← inferType source}"
  catch exception => return .error (← failure source exception)

/-- Plan one complete selected predicate. The retained rows are in their original
order with the selected row removed; generated rows are inserted at `insertionIndex`.
Only supplied records or native whole-bound rules are tried. Failed attempts and
ambiguous selection restore caller metavariables and environment declarations. -/
def plan (source : Expr) (retained : Array Expr) (rule? : Option Expr := none)
    (insertionIndex : Nat := 0) : MetaM (Except Error Result) :=
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
              point (mkApp source point) (planCore source retained rule? insertionIndex)
    catch exception => return .error (← failure source exception)

end Morew.Elab.NLP.Rewrite
