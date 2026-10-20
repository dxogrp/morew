import PTran.Conic
import PTran.Elab.Affine
import PTran.Elab.Reformulation.Presentation

/-!
# Checked affine row normalization

This internal API recognizes elaborated scalar and finite-vector equality and
inequality predicates. It returns a semantic cone row and a checked pointwise
equivalence, without changing a problem or its presentation.
-/

namespace PTran.Elab.Conic

open Lean Lean.Meta

/-- The semantic row and the proof relating it to the input predicate. -/
structure RowResult where
  /-- An expression of type `PTran.Conic.Constraint X`. -/
  constraint : Expr
  /-- Proof of `∀ x, constraint.Holds x ↔ predicate x`. -/
  pointwiseIff : Expr

private theorem normalizeEq
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (f g : X →ᵃ[ℝ] Y) (lhs rhs : X → Y)
    (hf : ∀ x, f x = lhs x) (hg : ∀ x, g x = rhs x) :
    ∀ x, (PTran.Conic.Constraint.eqZero (f - g)).Holds x ↔ lhs x = rhs x := by
  intro x
  rw [PTran.Conic.Constraint.holds_eqZero]
  change f x - g x = 0 ↔ lhs x = rhs x
  rw [hf, hg, sub_eq_zero]

private theorem normalizeLE
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [PartialOrder Y] [IsOrderedAddMonoid Y]
    [PosSMulMono ℝ Y] (f g : X →ᵃ[ℝ] Y) (lhs rhs : X → Y)
    (hf : ∀ x, f x = lhs x) (hg : ∀ x, g x = rhs x) :
    ∀ x, (PTran.Conic.Constraint.nonnegative (g - f)).Holds x ↔ lhs x ≤ rhs x := by
  intro x
  rw [PTran.Conic.Constraint.holds_nonnegative]
  change 0 ≤ g x - f x ↔ lhs x ≤ rhs x
  rw [hf, hg, sub_nonneg]

/-- Return the canonical real or coordinatewise real order, rather than using
an arbitrary local `LE` instance that happens to have the same operand type. -/
private def realOrder? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  if type.isConstOf ``Real then
    return some (mkConst ``Real.instLE)
  let .forallE name domain codomain _ := type | return none
  if codomain.hasLooseBVars then return none
  unless (← whnf codomain).isConstOf ``Real do return none
  unless (← whnf domain).isAppOfArity ``Fin 1 do return none
  let family := mkLambda name .default domain (mkConst ``Real)
  let orders := mkLambda name .default domain (mkConst ``Real.instLE)
  return some <| mkAppN (mkConst ``Pi.hasLe [Level.zero, Level.zero])
    #[domain, family, orders]

private def rowError (expression : Expr) (reason : MessageData)
    (label? : Option Name) : MetaM Affine.AffineError := do
  let reason := match label? with
    | none => m!"constraint: {reason}"
    | some label => m!"constraint `{label}`: {reason}"
  return { expression, reason := ← addMessageContext reason }

-- Relation instances and local aliases can hide metavariables in their local
-- declarations. Reject those before a definitional-equality check can solve
-- them and thereby certify only one possible completion of the input.
private partial def hasUnresolved (expression : Expr)
    (seen : FVarIdSet := {}) : MetaM Bool := do
  let expression ← instantiateMVars expression
  if expression.hasMVar then return true
  let mut seen := seen
  for id in (collectFVars {} expression).fvarIds do
    unless seen.contains id do
      seen := seen.insert id
      if let some declaration := (← getLCtx).find? id then
        if ← hasUnresolved declaration.type seen then return true
        if let some value := declaration.value? (allowNondep := true) then
          if ← hasUnresolved value seen then return true
  return false

private def normalizeRowCore (predicate : Expr) (config : Affine.Config)
    (label? : Option Name) : MetaM (Except Affine.AffineError RowResult) := do
  let predicate ← instantiateMVars predicate
  if ← hasUnresolved predicate then
    return .error (← rowError predicate "unresolved metavariables in predicate" label?)
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | return .error (← rowError predicate "expected a predicate on the decision space" label?)
  unless codomain == mkSort Level.zero do
    return .error (← rowError predicate "expected a predicate on the decision space" label?)
  withLocalDeclD `point domain fun point => do
    -- Preserve the typed relation head while eliminating language-level
    -- wrappers, including the product patterns used by the surface DSL.
    let body ← Affine.reduceStructure (mkApp predicate point)
    let args := body.getAppArgs
    let equality := body.isAppOfArity ``Eq 3
    let greaterEqual := body.isAppOfArity ``GE.ge 4
    unless equality || greaterEqual || body.isAppOfArity ``LE.le 4 do
      return .error (← rowError body
        m!"expected an equality or non-strict inequality; found {body}" label?)
    let target := args[0]!
    let some order ← realOrder? target
      | return .error (← rowError body "expected real scalar or finite-vector operands" label?)
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    unless equality do
      -- Compare the instance itself: a custom relation can agree with the
      -- standard order on these particular operands without being that order.
      unless ← isDefEq args[1]! order do
        return .error (← rowError body m!"unsupported order instance {args[1]!}" label?)
    let lhs ← mkLambdaFVars #[point] lhs
    let rhs ← mkLambdaFVars #[point] rhs
    let left ← Affine.reifyAffine lhs config
    if let .error error := left then
      return .error (← rowError error.expression m!"left-hand side: {error.reason}" label?)
    let .ok left := left
      | return .error (← rowError body "failed to recognize the left-hand side" label?)
    let right ← Affine.reifyAffine rhs config
    if let .error error := right then
      return .error (← rowError error.expression m!"right-hand side: {error.reason}" label?)
    let .ok right := right
      | return .error (← rowError body "failed to recognize the right-hand side" label?)
    let difference ← if equality || greaterEqual then
        mkAppM ``HSub.hSub #[left.map, right.map]
      else
        mkAppM ``HSub.hSub #[right.map, left.map]
    let constructor := if equality then
        ``PTran.Conic.Constraint.eqZero
      else ``PTran.Conic.Constraint.nonnegative
    let constraint ← instantiateMVars (← mkAppM constructor #[difference])
    let theoremName := if equality then ``normalizeEq else ``normalizeLE
    let proofArguments := if greaterEqual then
        #[right.map, left.map, rhs, lhs, right.pointwiseEquality, left.pointwiseEquality]
      else
        #[left.map, right.map, lhs, rhs, left.pointwiseEquality, right.pointwiseEquality]
    let pointwiseIff ← instantiateMVars (← mkAppM theoremName proofArguments)
    if constraint.hasMVar || pointwiseIff.hasMVar then
      return .error (← rowError body "row construction left unresolved metavariables" label?)
    let holds ← mkAppM ``PTran.Conic.Constraint.Holds #[constraint, point]
    let expected ← mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
    checkWithKernel constraint
    checkWithKernel pointwiseIff
    unless ← isDefEq (← inferType pointwiseIff) expected do
      return .error (← rowError body "row equivalence did not match the input predicate" label?)
    return .ok { constraint, pointwiseIff }

/-- Normalize an elaborated scalar or vector `=`, `≤`, or `≥` row.
The optional label supplies diagnostic context without depending on source
syntax or presentation metadata. -/
def normalizeRow (predicate : Expr) (config : Affine.Config := {})
    (label? : Option Name := none) : MetaM (Except Affine.AffineError RowResult) := do
  let saved ← saveState
  try
    withNewMCtxDepth <| normalizeRowCore predicate config label?
  catch error =>
    return .error (← rowError predicate error.toMessageData label?)
  finally
    saved.restore

/-- Recognize the real objective retained by a typed presentation. The explicit
optimization sense and order-dual annotation remain in the presentation. -/
def reifyObjective (presentation : Reformulation.PresentationState)
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError Affine.AffineResult) := do
  let saved ← saveState
  let fail (expression : Expr) (reason : MessageData) :
      MetaM (Except Affine.AffineError Affine.AffineResult) := do
    return .error {
      expression
      reason := ← addMessageContext m!"objective: {reason}"
    }
  try
    withNewMCtxDepth do
      if (← hasUnresolved presentation.valueType) ||
          (← hasUnresolved presentation.domainType) ||
          (← hasUnresolved presentation.objective) then
        return ← fail presentation.objective "unresolved metavariables in typed objective"
      unless (← whnf presentation.valueType).isConstOf ``Real do
        return ← fail presentation.objective "expected a real-valued objective"
      let expected ← mkArrow presentation.domainType presentation.valueType
      unless ← isDefEq (← inferType presentation.objective) expected do
        return ← fail presentation.objective
          "objective function does not match its presentation domain and value type"
      match ← Affine.reifyAffine presentation.objective config with
      | .ok result => return .ok result
      | .error error => fail error.expression error.reason
  catch error =>
    fail presentation.objective error.toMessageData
  finally
    saved.restore

/-- Normalize a typed named constraint, retaining its label in diagnostics. -/
def normalizeConstraint (entry : Reformulation.ConstraintEntry)
    (config : Affine.Config := {}) : MetaM (Except Affine.AffineError RowResult) :=
  normalizeRow entry.predicate config (some entry.name)

end PTran.Elab.Conic
