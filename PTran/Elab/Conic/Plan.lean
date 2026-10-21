import PTran.Elab.Conic
import PTran.Transform

/-!
# Shared exact conic replacement planning

Inspect custom representations, split ordered target rows, and certify each row.
Operation recognizers and the surface runner share this implementation.
-/

namespace PTran.Elab.Conic.Plan

open Lean Lean.Meta

/-- A complete exact replacement, before presentation names are allocated. -/
structure Result where
  /-- A checked `ExactConstraintLift sourcePredicate`. -/
  lift : Expr
  /-- The auxiliary type, with `Unit` erased. -/
  auxiliary? : Option Expr
  /-- The original domain, or its product with the auxiliary type. -/
  nextDomain : Expr
  /-- Replacement predicates in deterministic conjunction order. -/
  rowPredicates : Array Expr
  /-- The instantiated lift target is equivalent to the row conjunction. -/
  targetIff : Expr
  /-- Checked affine cone rows corresponding to `rowPredicates`. -/
  certifiedRows : Array RowResult

private def Result.replaceFVar (result : Result) (binding value : Expr) : Result :=
  let replace := fun expression : Expr => expression.replaceFVars #[binding] #[value]
  { lift := replace result.lift
    auxiliary? := result.auxiliary?.map replace
    nextDomain := replace result.nextDomain
    rowPredicates := result.rowPredicates.map replace
    targetIff := replace result.targetIff
    certifiedRows := result.certifiedRows.map fun row => {
      constraint := replace row.constraint
      pointwiseIff := replace row.pointwiseIff } }

/-- Retain source indexing evidence while constructing a checked plan. -/
def withFiniteInstances (instances : List Expr) (action : MetaM Result) :
    MetaM Result := do
  match instances with
  | [] => action
  | inst :: rest =>
    withLetDecl `_conicFinite (← inferType inst) inst fun binding => do
      let result ← withFiniteInstances rest action
      return result.replaceFVar binding inst

-- Independent source lets can carry denominator proofs needed by generated
-- rows. Keep those declarations in scope throughout planning, then substitute
-- their values into every returned expression.
/-- Retain independent source lets during exact-rule construction. -/
partial def withPredicateEvidence (point body : Expr)
    (action : MetaM Result) : MetaM Result := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← withPredicateEvidence point (rest.instantiate1 value) action
    withLetDecl name type value (nondep := nondep) fun binding => do
      let result ← withPredicateEvidence point (rest.instantiate1 binding) action
      return result.replaceFVar binding value
  else
    action

private theorem emptyLeft (p : Prop) : True ∧ p ↔ p :=
  ⟨fun h => h.2, fun h => ⟨True.intro, h⟩⟩

private theorem emptyRight (p : Prop) : p ∧ True ↔ p :=
  ⟨fun h => h.1, fun h => ⟨h, True.intro⟩⟩

private theorem appendHead (p q r s : Prop) (h : q ∧ r ↔ s) :
    (p ∧ q) ∧ r ↔ p ∧ s :=
  and_assoc.trans (and_congr Iff.rfl h)

private def conjunction : List Expr → Expr
  | [] => mkConst ``True
  | [p] => p
  | p :: rest => mkApp2 (mkConst ``And) p (conjunction rest)

private partial def appendIff (left right : List Expr) : MetaM Expr := do
  match left, right with
  | [], _ => mkAppM ``emptyLeft #[conjunction right]
  | _, [] => mkAppM ``emptyRight #[conjunction left]
  | [_], _ => pure <| mkApp (mkConst ``Iff.rfl) (conjunction (left ++ right))
  | p :: rest, _ =>
      mkAppM ``appendHead #[p, conjunction rest, conjunction right,
        conjunction (rest ++ right), ← appendIff rest right]

-- Adapters can leave another representation's target projection at the head.
-- Expose only these record fields, stopping before arbitrary predicate helpers
-- or arithmetic operands are unfolded.
private partial def exposeTarget (body : Expr) : MetaM Expr := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  let head := body.getAppFn
  let prefixSize? := match head.constName? with
    | some ``PTran.ExactConstraintLift.target => some 3
    | some ``PTran.GraphRepresentation.target => some 4
    | some ``PTran.EpigraphRepresentation.target => some 5
    | some ``PTran.HypographRepresentation.target => some 5
    | _ => none
  if let some prefixSize := prefixSize? then
    let args := body.getAppArgs
    if args.size >= prefixSize then
      let partialTarget := mkAppN head (args.extract 0 prefixSize)
      let reduced ← whnf partialTarget
      unless reduced == partialTarget do
        return ← exposeTarget (mkAppN reduced (args.extract prefixSize args.size))
  return body

private partial def splitTarget (body : Expr) : MetaM (List Expr × Expr) := do
  let body ← exposeTarget body
  if let .letE name type value rest _ := body then
    -- The decomposition proof's type can depend on this value even when the
    -- original predicate's type does not. Rebuild it as a dependent let.
    return ← withLetDecl name type value fun binding => do
      let (rows, proof) ← splitTarget (rest.instantiate1 binding)
      -- Keep nondependent lets as lets, rather than abstracting them into lambdas.
      let rows ← rows.mapM fun row =>
        mkLetFVars #[binding] row (usedLetOnly := false) (generalizeNondepLet := false)
      let proof ← mkLetFVars #[binding] proof
        (usedLetOnly := false) (generalizeNondepLet := false)
      return (rows, proof)
  if body.isConstOf ``True then
    return ([], mkApp (mkConst ``Iff.rfl) body)
  if body.isAppOfArity ``And 2 then
    let args := body.getAppArgs
    let (left, hl) ← splitTarget args[0]!
    let (right, hr) ← splitTarget args[1]!
    let split ← mkAppM ``and_congr #[hl, hr]
    let combined ← mkAppM ``Iff.trans #[split, ← appendIff left right]
    return (left ++ right, combined)
  unless body.isAppOfArity ``Eq 3 || body.isAppOfArity ``LE.le 4 ||
      body.isAppOfArity ``GE.ge 4 || body.isAppOfArity ``Membership.mem 5 do
    throwError "unsupported exact target predicate {body}; expected True, conjunctions, affine equalities and non-strict inequalities, or supported cone memberships"
  return ([body], mkApp (mkConst ``Iff.rfl) body)

-- Do not let unification specialize a caller's unresolved local declarations.
/-- Detect unresolved expressions, including evidence hidden in local declarations. -/
partial def unresolved (expression : Expr) (seen : FVarIdSet := {}) :
    MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then return true
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    unless seen.contains id do
      seen := seen.insert id
      let declaration ← id.getDecl
      if ← unresolved declaration.type seen then return true
      if let some value := declaration.value? (allowNondep := true) then
        if ← unresolved value seen then return true
  return false

/-- Read the decision domain of a fully elaborated predicate. -/
def predicateDomain (predicate : Expr) : MetaM Expr := do
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | throwError "expected a predicate on the current decision domain"
  unless codomain == mkSort .zero do
    throwError "expected a predicate on the current decision domain"
  return domain

/-- Check that a supplied lift describes the complete selected predicate. -/
def checkLift (source lift : Expr) : MetaM Expr := do
  let type ← whnf (← inferType lift)
  unless type.isAppOfArity ``PTran.ExactConstraintLift 2 do
    throwError "expected an exact constraint lift"
  unless ← isDefEq type.getAppArgs[1]! source do
    throwError "the supplied exact certificate does not describe the entire selected predicate"
  let lift ← instantiateMVars lift
  if ← unresolved lift then
    throwError "the exact certificate contains unresolved metavariables; supply its input and bound maps explicitly"
  checkWithKernel lift
  return lift

private def adaptRepresentation (source domain rule : Expr) (adapter : Name)
    (inputType outputType : Expr) : MetaM Expr := do
  let input ← mkFreshExprMVar (← mkArrow domain inputType)
  let output ← mkFreshExprMVar (← mkArrow domain outputType)
  let lift ← mkAppM adapter #[rule, input, output]
  checkLift source lift

/-- Adapt one of the supported exact representation records to a selected predicate. -/
def customLift (source domain rule : Expr) : MetaM Expr := do
  let type ← whnf (← inferType rule)
  let args := type.getAppArgs
  if type.isAppOfArity ``PTran.ExactConstraintLift 2 then
    return ← checkLift source rule
  if type.isAppOfArity ``PTran.GraphRepresentation 3 then
    let saved ← saveState
    try
      return ← adaptRepresentation source domain rule
        ``PTran.GraphRepresentation.toExactConstraintLift args[0]! args[1]!
    catch _ =>
      saved.restore
      return ← adaptRepresentation source domain rule
        ``PTran.GraphRepresentation.toExactConstraintLiftSymm args[0]! args[1]!
  if type.isAppOfArity ``PTran.EpigraphRepresentation 4 then
    return ← adaptRepresentation source domain rule
      ``PTran.EpigraphRepresentation.toExactConstraintLift args[0]! args[1]!
  if type.isAppOfArity ``PTran.HypographRepresentation 4 then
    return ← adaptRepresentation source domain rule
      ``PTran.HypographRepresentation.toExactConstraintLift args[0]! args[1]!
  throwError "expected an ExactConstraintLift, GraphRepresentation, EpigraphRepresentation, or HypographRepresentation for the entire selected predicate"

/-- Certify each replacement row without changing its presentation predicate. -/
def certifyRows (predicates : Array Expr) (config : Affine.Config := {}) :
    MetaM (Array RowResult) := do
  predicates.mapM fun predicate => do
    match ← normalizeRow predicate config with
    | .ok row => pure row
    | .error error => throwError "generated row: {error.reason}"

private def finishCore (source domain lift : Expr) (config : Affine.Config) : MetaM Result := do
  let auxiliary ← whnf (← mkAppM ``PTran.ExactConstraintLift.Auxiliary #[lift])
  let noAuxiliary ← isDefEq auxiliary (mkConst ``Unit)
  let auxiliary? := if noAuxiliary then none else some auxiliary
  let nextDomain ← if noAuxiliary then pure domain else mkAppM ``Prod #[domain, auxiliary]
  unless ← Affine.isSupportedSpace nextDomain do
    throwError "unsupported exact-lift decision space {nextDomain}; expected real scalars, products, or finite function spaces"
  let targetFunction ← whnf (← mkAppM ``PTran.ExactConstraintLift.target #[lift])
  let (rowPredicates, targetIff) ← withLocalDeclD `point nextDomain fun point => do
    let target := if noAuxiliary then mkApp2 targetFunction point (mkConst ``Unit.unit)
      else mkApp2 targetFunction (.proj ``Prod 0 point) (.proj ``Prod 1 point)
    let (bodies, proof) ← splitTarget target
    let rows ← bodies.toArray.mapM fun body => mkLambdaFVars #[point] body
    return (rows, ← mkLambdaFVars #[point] proof)
  let certifiedRows ← certifyRows rowPredicates config
  checkWithKernel targetIff
  let expected ← withLocalDeclD `point nextDomain fun point => do
    let target ← if noAuxiliary then
        mkAppM ``PTran.ExactConstraintLift.target #[lift, point, mkConst ``Unit.unit]
      else
        mkAppM ``PTran.ExactConstraintLift.target
          #[lift, .proj ``Prod 0 point, .proj ``Prod 1 point]
    let rows := rowPredicates.toList.map (mkApp · point)
    mkForallFVars #[point] (mkApp2 (mkConst ``Iff) target (conjunction rows))
  unless ← isDefEq (← inferType targetIff) expected do
    throwError "internal error: target decomposition does not match the exact lift"
  let _ ← checkLift source lift
  return { lift, auxiliary?, nextDomain, rowPredicates, targetIff, certifiedRows }

/-- Split and certify every row of an exact lift. -/
def finish (source domain lift : Expr) (config : Affine.Config) : MetaM Result := do
  let target ← whnf (← mkAppM ``PTran.ExactConstraintLift.target #[lift])
  withFiniteInstances (← Affine.sourceFiniteInstances target).toList do
    finishCore source domain lift config

/-- Plan one entire selected predicate. A supplied record bypasses automatic
operation matching, but every resulting row still undergoes affine checking.
Caller metavariables and the environment are restored on failure. -/
def plan (automaticLift : Expr → Expr → MetaM Expr) (sourcePredicate : Expr) (rule? : Option Expr := none)
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Result) :=
  Affine.withIsolatedMVars do
    try
      let source ← instantiateMVars sourcePredicate
      if ← unresolved source then throwError "unresolved metavariables in the selected predicate"
      let domain ← predicateDomain source
      let result ← withFiniteInstances (← Affine.sourceFiniteInstances source).toList do
        withLocalDeclD `point domain fun point =>
          withPredicateEvidence point (mkApp source point) do
            let lift ← match rule? with
              | none => automaticLift source domain
              | some rule => customLift source domain (← instantiateMVars rule)
            finish source domain lift config
      return .ok result
    catch error =>
      return .error {
        expression := sourcePredicate
        reason := ← addMessageContext error.toMessageData
      }

end PTran.Elab.Conic.Plan
