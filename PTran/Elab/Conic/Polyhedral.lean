import PTran.Conic.Polyhedral
import PTran.Elab.Atom
import PTran.Elab.Conic
import PTran.Transform

/-!
# Checked plans for exact polyhedral constraint replacements

The planner consumes a typed predicate, produces an exact lift, and checks every
replacement row with the ordinary affine certifier. Presentation names and
problem updates belong to its callers.
-/

namespace PTran.Elab.Conic.Polyhedral

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

private def withFiniteInstances (instances : List Expr) (action : MetaM Result) :
    MetaM Result := do
  match instances with
  | [] => action
  | inst :: rest =>
    withLetDecl `_polyhedralFinite (← inferType inst) inst fun binding => do
      let result ← withFiniteInstances rest action
      return result.replaceFVar binding inst

-- Independent source lets can carry denominator proofs needed by generated
-- rows. Keep those declarations in scope throughout planning, then substitute
-- their values into every returned expression.
private partial def withPredicateEvidence (point body : Expr)
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
  if let .letE name type value rest nondep := body then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      let (rows, proof) ← splitTarget (rest.instantiate1 binding)
      let rows ← rows.mapM fun row => mkLetFVars #[binding] row (usedLetOnly := false)
      let proof ← mkLetFVars #[binding] proof (usedLetOnly := false)
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
      body.isAppOfArity ``GE.ge 4 do
    throwError "unsupported exact target predicate {body}; expected True, conjunctions, or affine equalities and non-strict inequalities"
  return ([body], mkApp (mkConst ``Iff.rfl) body)

-- Do not let unification specialize a caller's unresolved local declarations.
private partial def unresolved (expression : Expr) (seen : FVarIdSet := {}) :
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

private def predicateDomain (predicate : Expr) : MetaM Expr := do
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | throwError "expected a predicate on the current decision domain"
  unless codomain == mkSort .zero do
    throwError "expected a predicate on the current decision domain"
  return domain

private def checkLift (source lift : Expr) : MetaM Expr := do
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

private def customLift (source domain rule : Expr) : MetaM Expr := do
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

private def isRealVector (type : Expr) : MetaM Bool := do
  let type ← whnf type
  let .forallE _ index body _ := type | return false
  if body.hasLooseBVars then return false
  return (← whnf index).isAppOfArity ``Fin 1 && (← whnf body).isConstOf ``Real

private def theoremSides (proof : Expr) : MetaM (Expr × Expr) := do
  let type ← inferType proof
  unless type.isAppOfArity ``Iff 2 do throwError "internal error: expected an exact iff theorem"
  return (type.getAppArgs[0]!, type.getAppArgs[1]!)

-- Compare the operation instances themselves before checking the theorem's
-- full predicate. A custom operation that agrees only at these operands is
-- not evidence that the native rule applies.
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

private def finiteExtremumProof (point operation bound : Expr) (minimum : Bool) :
    MetaM Expr := do
  let args := operation.getAppArgs
  unless args.size == 6 do throwError "unsupported finite extremum {operation}"
  if ← Affine.depends point args[3]! then
    throwError "the finite extremum's index set depends on a decision variable"
  let theoremName := if minimum then ``PTran.Conic.Polyhedral.le_inf'_iff
    else ``PTran.Conic.Polyhedral.sup'_le_iff
  let proof ← mkAppM theoremName #[args[3]!, args[4]!, args[5]!, bound]
  let (lhs, _) ← theoremSides proof
  let expected := lhs.getAppArgs[if minimum then 3 else 2]!
  sameOperationPrefix operation expected 3
  return proof

private def normProof (operation bound : Expr) : MetaM Expr := do
  let args := operation.getAppArgs
  unless operation.isAppOfArity ``Norm.norm 3 do
    throwError "unsupported norm bound {operation}"
  let vector := args[2]!
  let proof ← if ← isRealVector (← inferType vector) then
      mkAppM ``PTran.Conic.Polyhedral.norm_le_iff #[vector, bound]
    else do
      let vector ← Affine.reduceStructure vector
      unless vector.isAppOfArity ``WithLp.toLp 3 do
        throwError "expected the native norm of Fin n → ℝ or WithLp.toLp 1/∞ of such a vector"
      let lpArgs := vector.getAppArgs
      unless ← isRealVector (← inferType lpArgs[2]!) do
        throwError "expected a Fin n → ℝ vector inside WithLp.toLp"
      let saved ← saveState
      let topProof ← mkAppM ``PTran.Conic.Polyhedral.norm_toLp_top_le_iff
        #[lpArgs[2]!, bound]
      let (topSource, _) ← theoremSides topProof
      let expectedTop := topSource.getAppArgs[2]!
      if ← isDefEq vector expectedTop.getAppArgs[2]! then
        pure topProof
      else
        saved.restore
        let oneProof ← mkAppM ``PTran.Conic.Polyhedral.norm_toLp_one_le_iff
          #[lpArgs[2]!, bound]
        let (oneSource, _) ← theoremSides oneProof
        unless ← isDefEq vector oneSource.getAppArgs[2]!.getAppArgs[2]! do
          throwError "unsupported norm exponent; expected 1 or ∞"
        pure oneProof
  let (source, _) ← theoremSides proof
  sameOperationPrefix operation source.getAppArgs[2]! 1
  return proof

private def automaticProof (point body : Expr) : MetaM Expr := do
  let body ← Affine.reduceStructure body
  let greaterEqual := body.isAppOfArity ``GE.ge 4
  unless greaterEqual || body.isAppOfArity ``LE.le 4 do
    throwError "no supported exact polyhedral rule for {body}; expected an upper epigraph bound or lower hypograph bound"
  let args := body.getAppArgs
  unless ← isDefEq args[0]! (mkConst ``Real) do
    throwError "expected a real scalar bound for an exact polyhedral rule"
  unless ← isDefEq args[1]! (mkConst ``Real.instLE) do
    throwError "unsupported order instance in the selected predicate"
  let left ← Affine.reduceStructure args[if greaterEqual then 3 else 2]!
  let right ← Affine.reduceStructure args[if greaterEqual then 2 else 3]!
  if let some operation ← Atom.recognizeAtom? left then
    let operands := operation.operands
    match operation.kind with
    | .abs => return ← mkAppM ``PTran.Conic.Polyhedral.abs_le_iff #[operands[0]!, right]
    | .pos => return ← mkAppM ``PTran.Conic.Polyhedral.posPart_le_iff #[operands[0]!, right]
    | .maximum =>
        return ← mkAppM ``PTran.Conic.Polyhedral.max_le_iff
          #[operands[0]!, operands[1]!, right]
    | _ => pure ()
  if let some operation ← Atom.recognizeAtom? right then
    if operation.kind == .minimum then
      return ← mkAppM ``PTran.Conic.Polyhedral.le_min_iff
        #[operation.operands[0]!, operation.operands[1]!, left]
  if left.isAppOfArity ``Finset.sup' 6 then
    return ← finiteExtremumProof point left right false
  if right.isAppOfArity ``Finset.inf' 6 then
    return ← finiteExtremumProof point right left true
  if left.isAppOfArity ``Norm.norm 3 then
    return ← normProof left right
  throwError "no supported exact polyhedral rule for {body}; expected abs, positive part, maximum, minimum, a finite extremum, or a supported norm in its exact orientation"

private def automaticLift (source domain : Expr) : MetaM Expr :=
  withLocalDeclD `point domain fun point => do
    let body ← Affine.reduceStructure (mkApp source point)
    let proof ← automaticProof point body
    let (provedSource, target) ← theoremSides proof
    unless ← isDefEq provedSource body do
      throwError "the exact rule does not describe the entire selected predicate"
    let pointwise ← mkLambdaFVars #[point] proof
    let lift ← if target.isAppOfArity ``Exists 2 then do
        let args := target.getAppArgs
        if ← Affine.depends point args[0]! then
          throwError "the auxiliary type depends on a decision variable"
        let target ← mkLambdaFVars #[point] args[1]!
        mkAppM ``PTran.ExactConstraintLift.mk #[args[0]!, target, pointwise]
      else do
        let target ← mkLambdaFVars #[point] target
        mkAppM ``PTran.ExactConstraintLift.ofIff #[target, pointwise]
    checkLift source lift

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
  let mut certifiedRows := #[]
  for predicate in rowPredicates do
    match ← normalizeRow predicate config with
    | .ok row => certifiedRows := certifiedRows.push row
    | .error error => throwError "generated row: {error.reason}"
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

private def finish (source domain lift : Expr) (config : Affine.Config) : MetaM Result := do
  let target ← whnf (← mkAppM ``PTran.ExactConstraintLift.target #[lift])
  withFiniteInstances (← Affine.sourceFiniteInstances target).toList do
    finishCore source domain lift config

/-- Plan one entire selected predicate. A supplied record bypasses automatic
operation matching, but every resulting row still undergoes affine checking.
Caller metavariables and the environment are restored on failure. -/
def plan (sourcePredicate : Expr) (rule? : Option Expr := none)
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

end PTran.Elab.Conic.Polyhedral
