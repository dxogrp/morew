/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic
import Morew.Elab.Affine
import Morew.Elab.State
import Morew.Elab.Conic.Space
import Morew.Elab.Conic.Evidence
import Morew.Elab.Conic.Normalize
import Morew.Elab.Conic.Symmetry
import Morew.Conic.Power.Cone
import Morew.Elab.Reformulation.Presentation
import Morew.Elab.Expr

/-!
# Checked affine row normalization

This internal API recognizes elaborated scalar and finite-vector equality and
inequality predicates, native second-order, exponential, power and PSD cone membership,
and ordinary real matrix positive semidefiniteness with global symmetry evidence.
A finite family of exponential or power memberships remains one quantified presentation
row and is certified against the finite product cone. The API returns a semantic
cone row and a checked pointwise equivalence, without changing a problem or its
presentation.
-/

namespace Morew.Elab.Conic

open Lean Lean.Meta

/-- The semantic row and the proof relating it to the input predicate. -/
structure RowResult where
  /-- An expression of type `Morew.Conic.Constraint X`. -/
  constraint : Expr
  /-- Proof of `∀ x, constraint.Holds x ↔ predicate x`. -/
  pointwiseIff : Expr
  /-- Checked source-to-membership conversion, retained for terminal normalization. -/
  normalization? : Option PredicateNormalization := none

/-- Transform every expression in a row, including its cached normalization evidence. -/
def RowResult.mapExprM (row : RowResult) (f : Expr → MetaM Expr) : MetaM RowResult := do
  return {
    constraint := ← f row.constraint
    pointwiseIff := ← f row.pointwiseIff
    normalization? := ← row.normalization?.mapM fun normalized => do
      return { normalized with
        predicate := ← f normalized.predicate
        pointwiseIff := ← f normalized.pointwiseIff }
  }

/-- Rebase a row and all its cached evidence onto a new variable context. -/
def RowResult.replaceFVars (row : RowResult) (oldVars newVars : Array Expr) : RowResult := {
  constraint := row.constraint.replaceFVars oldVars newVars
  pointwiseIff := row.pointwiseIff.replaceFVars oldVars newVars
  normalization? := row.normalization?.map fun normalized => {
    normalized with
    predicate := normalized.predicate.replaceFVars oldVars newVars
    pointwiseIff := normalized.pointwiseIff.replaceFVars oldVars newVars }
}

-- Fix the real normed-space instances before subtracting. The certified maps
-- can use definitionally equal instance aliases that typeclass search alone
-- does not unfold when asked to infer a heterogeneous subtraction operation.
private def subtractMaps
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f g : X →ᵃ[ℝ] Y) : X →ᵃ[ℝ] Y := f - g

private theorem normalizeEq
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (f g : X →ᵃ[ℝ] Y) (lhs rhs : X → Y)
    (hf : ∀ x, f x = lhs x) (hg : ∀ x, g x = rhs x) :
    ∀ x, (Morew.Conic.Constraint.eqZero (f - g)).Holds x ↔ lhs x = rhs x := by
  intro x
  rw [Morew.Conic.Constraint.holds_eqZero]
  change f x - g x = 0 ↔ lhs x = rhs x
  rw [hf, hg, sub_eq_zero]

private theorem normalizeLE
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [PartialOrder Y] [IsOrderedAddMonoid Y]
    [PosSMulMono ℝ Y] (f g : X →ᵃ[ℝ] Y) (lhs rhs : X → Y)
    (hf : ∀ x, f x = lhs x) (hg : ∀ x, g x = rhs x) :
    ∀ x, (Morew.Conic.Constraint.nonnegative (g - f)).Holds x ↔ lhs x ≤ rhs x := by
  intro x
  rw [Morew.Conic.Constraint.holds_nonnegative]
  change 0 ≤ g x - f x ↔ lhs x ≤ rhs x
  rw [hf, hg, sub_nonneg]

-- This fixed-context template retains the actual canonical membership
-- instance. Comparing only the resulting propositions would also accept a
-- custom membership relation that happens to agree at the selected tuple.
private def canonicalMembership (cone : Morew.Conic.Cone) (value : cone.Space) : Prop :=
  value ∈ cone.carrier

private def canonicalPowerMembership (α : ℝ) (value : ℝ × ℝ × ℝ) : Prop :=
  value ∈ Morew.Conic.Cone.powerSet α

private def powerExponentRange (α : ℝ) : Prop := 0 < α ∧ α < 1

private theorem normalizeMembership
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cone : Morew.Conic.Cone) (map : X →ᵃ[ℝ] cone.Space)
    (source : X → cone.Space) (h : ∀ x, map x = source x) :
    ∀ x, (Morew.Conic.Constraint.mk cone map).Holds x ↔ source x ∈ cone.carrier := by
  intro x
  change map x ∈ cone.carrier ↔ source x ∈ cone.carrier
  rw [h x]

private def canonicalPositiveSemidefinite (n : Nat)
    (value : Matrix (Fin n) (Fin n) ℝ) : Prop := value.PosSemidef

private theorem positiveSemidefiniteMembership {n : Nat}
    (value : Matrix (Fin n) (Fin n) ℝ) (symmetric : value.IsSymm) :
    value.PosSemidef ↔ Morew.Conic.SymmetricMatrix.ofMatrix value symmetric ∈
      (Morew.Conic.Cone.positiveSemidefinite n).carrier := Iff.rfl

private def canonicalScalarZeroMembership (value : ℝ) : Prop :=
  value ∈ ({0} : Set ℝ)

private def canonicalVectorZeroMembership (n : Nat) (value : Fin n → ℝ) : Prop :=
  value ∈ ({0} : Set (Fin n → ℝ))

private def canonicalScalarZero : ℝ := @Zero.zero ℝ inferInstance

private def canonicalVectorZero (n : Nat) : Fin n → ℝ :=
  @Zero.zero (Fin n → ℝ) inferInstance

private theorem normalizeZeroMembership
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] (map : X →ᵃ[ℝ] Y)
    (source : X → Y) (h : ∀ x, map x = source x) :
    ∀ x, (Morew.Conic.Constraint.eqZero map).Holds x ↔ source x ∈ ({0} : Set Y) := by
  intro x
  rw [Morew.Conic.Constraint.holds_eqZero, h x, Set.mem_singleton_iff]

private theorem normalizeExponentialFamily
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : Nat) (map : X →ᵃ[ℝ] (Morew.Conic.Cone.exponentialProduct n).Space)
    (source : X → Fin n → ℝ × ℝ × ℝ) (h : ∀ x, map x = source x) :
    ∀ x, (Morew.Conic.Constraint.mk (Morew.Conic.Cone.exponentialProduct n) map).Holds x ↔
      ∀ i, source x i ∈ Morew.Conic.Cone.exponential.carrier := by
  intro x
  change map x ∈ (Morew.Conic.Cone.exponentialProduct n).carrier ↔ _
  rw [h x]
  exact Morew.Conic.Cone.mem_exponentialProduct (source x)

private theorem normalizePowerFamily
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : Nat) (α : Fin n → ℝ) (hα : ∀ i, 0 < α i ∧ α i < 1)
    (map : X →ᵃ[ℝ] (Morew.Conic.Cone.powerProduct n α hα).Space)
    (source : X → Fin n → ℝ × ℝ × ℝ) (h : ∀ x, map x = source x) :
    ∀ x, (Morew.Conic.Constraint.mk (Morew.Conic.Cone.powerProduct n α hα) map).Holds x ↔
      ∀ i, source x i ∈ Morew.Conic.Cone.powerSet (α i) := by
  intro x
  change map x ∈ (Morew.Conic.Cone.powerProduct n α hα).carrier ↔ _
  rw [h x]
  exact Morew.Conic.Cone.mem_powerProduct α hα (source x)

/-- Return the canonical real or coordinatewise real order, rather than using
an arbitrary local `LE` instance that happens to have the same operand type. -/
private def realOrder? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  if type.isConstOf ``Real then
    return some (mkConst ``Real.instLE)
  let .forallE name domain codomain _ := type | return none
  let codomain ← whnf codomain
  if codomain.hasLooseBVars then return none
  unless codomain.isConstOf ``Real do return none
  unless (← whnf domain).isAppOfArity ``Fin 1 do return none
  let family := mkLambda name .default domain (mkConst ``Real)
  let orders := mkLambda name .default domain (mkConst ``Real.instLE)
  return some <| mkAppN (mkConst ``Pi.hasLe [Level.zero, Level.zero])
    #[domain, family, orders]

private def rowError (expression : Expr) (reason : MessageData)
    (label? : Option Name) : MetaM Expr.Error := do
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

-- Keep decision-independent lets available, including denominator proofs and
-- instances. Dependent lets must be substituted before abstracting the point;
-- independent values are substituted into both results before leaving scope.
private partial def withPredicateLets (point body : Expr)
    (action : Expr → MetaM (Except Expr.Error RowResult)) :
    MetaM (Except Expr.Error RowResult) := do
  let body ← Expr.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Expr.depends point type) || (← Expr.depends point value) then
      return ← withPredicateLets point (rest.instantiate1 value) action
    withLetDecl name type value (nondep := nondep) fun binding => do
      match ← withPredicateLets point (rest.instantiate1 binding) action with
      | .error error => return .error error
      | .ok result =>
        return .ok (← result.mapExprM (·.replaceFVarsM #[binding] #[value]))
  else
    action body

private def membershipData (point body : Expr) (label? : Option Name)
    (index? : Option Expr := none) :
    MetaM (Except Expr.Error (Expr × Expr)) := do
  let args := body.getAppArgs
  let carrier ← Expr.reduceStructure args[3]!
  if carrier.isAppOfArity ``Morew.Conic.Cone.powerSet 1 then
    let exponent := carrier.getAppArgs[0]!
    if ← Expr.depends point exponent then
      return .error (← rowError body "power cone exponent depends on the decision point" label?)
    let value := args[4]!
    let template := (← getConstInfo ``canonicalPowerMembership).value!
    let canonical := (mkAppN template #[exponent, value]).headBeta
    unless ← isDefEq args[2]! canonical.getAppArgs[2]! do
      return .error (← rowError body m!"unsupported membership instance {args[2]!}" label?)
    unless ← isDefEq body canonical do
      return .error (← rowError body "membership does not match the canonical power cone set" label?)
    let range := (mkApp (← getConstInfo ``powerExponentRange).value! exponent).headBeta
    let some evidence ← Evidence.proveIndependent? point range index?
      | return .error (← rowError body
          m!"missing independent power cone exponent evidence: required 0 < {exponent} ∧ {exponent} < 1" label?)
    let cone ← mkAppM ``Morew.Conic.Cone.power #[exponent, evidence]
    checkWithKernel cone
    return .ok (cone, value)
  let carrier := if carrier.isConstOf ``Morew.Conic.Cone.nonnegativeScalarCarrier then
      mkApp (mkConst ``Morew.Conic.Cone.carrier)
        (mkConst ``Morew.Conic.Cone.nonnegativeScalar)
    else carrier
  unless carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1 do
    return .error (← rowError body "expected native supported cone membership" label?)
  let cone ← Expr.reduceStructure carrier.getAppArgs[0]!
  unless cone.isAppOfArity ``Morew.Conic.Cone.secondOrder 1 ||
      cone.isAppOfArity ``Morew.Conic.Cone.rotatedSecondOrder 1 ||
      cone.isAppOfArity ``Morew.Conic.Cone.zero 1 ||
      cone.isAppOfArity ``Morew.Conic.Cone.nonnegative 1 ||
      cone.isConstOf ``Morew.Conic.Cone.nonnegativeScalar ||
      cone.isConstOf ``Morew.Conic.Cone.exponential ||
      cone.isAppOfArity ``Morew.Conic.Cone.power 2 ||
      cone.isAppOfArity ``Morew.Conic.Cone.powerProduct 3 ||
      cone.isAppOfArity ``Morew.Conic.Cone.exponentialProduct 1 ||
      cone.isAppOfArity ``Morew.Conic.Cone.positiveSemidefinite 1 do
    return .error (← rowError body m!"unsupported cone {cone}" label?)
  let power := cone.isAppOfArity ``Morew.Conic.Cone.power 2 ||
    cone.isAppOfArity ``Morew.Conic.Cone.powerProduct 3
  if power && (← Evidence.hasPlaceholders cone) then
    return .error (← rowError body "power cone contains unresolved placeholders" label?)
  if ← Expr.depends point cone then
    let description := if power then
      "power cone parameter depends on the decision point"
      else "cone dimension depends on the decision point"
    return .error (← rowError body description label?)
  let value := args[4]!
  let template := (← getConstInfo ``canonicalMembership).value!
  let canonical := (mkAppN template #[cone, value]).headBeta
  let canonicalArgs := canonical.getAppArgs
  unless ← isDefEq args[2]! canonicalArgs[2]! do
    return .error (← rowError body m!"unsupported membership instance {args[2]!}" label?)
  unless ← isDefEq body canonical do
    return .error (← rowError body "membership does not match the canonical cone" label?)
  return .ok (cone, value)

/-- Recover native scalar or finite-vector nonnegative-cone coordinates after checking the
membership instance. This does not unfold wrappers or certify affinity. -/
def nonnegativeValue? (point body : Expr) : MetaM (Option Expr) := do
  let result : Except Unit Expr ← State.withIsolatedMVars do
    if !(body.isAppOfArity ``Membership.mem 5) || (← hasUnresolved body) then
      return .error ()
    match ← membershipData point body none with
    | .ok (cone, value) =>
        return if cone.isConstOf ``Morew.Conic.Cone.nonnegativeScalar ||
            cone.isAppOfArity ``Morew.Conic.Cone.nonnegative 1 then .ok value else .error ()
    | .error _ => return .error ()
  return result.toOption

private def singletonZeroData (point body : Expr) (label? : Option Name) :
    MetaM (Except Expr.Error Expr) := do
  let args := body.getAppArgs
  let value := args[4]!
  let target ← whnf args[0]!
  let (canonical, explicitZero) ← if target.isConstOf ``Real then do
      pure ((mkApp (← getConstInfo ``canonicalScalarZeroMembership).value! value).headBeta,
        (← getConstInfo ``canonicalScalarZero).value!)
    else do
      let .forallE _ index range _ := target
        | return .error (← rowError body "expected a real scalar or finite-vector zero singleton" label?)
      let range ← whnf range
      unless !range.hasLooseBVars && range.isConstOf ``Real do
        return .error (← rowError body "expected a real scalar or finite-vector zero singleton" label?)
      let index ← whnf index
      unless index.isAppOfArity ``Fin 1 do
        return .error (← rowError body "expected a finite-vector zero singleton" label?)
      let dimension := index.getAppArgs[0]!
      if ← Expr.depends point dimension then
        return .error (← rowError body "cone dimension depends on the decision point" label?)
      pure ((mkAppN (← getConstInfo ``canonicalVectorZeroMembership).value!
        #[dimension, value]).headBeta,
        (mkApp (← getConstInfo ``canonicalVectorZero).value! dimension).headBeta)
  let canonicalArgs := canonical.getAppArgs
  unless ← isDefEq args[2]! canonicalArgs[2]! do
    return .error (← rowError body m!"unsupported membership instance {args[2]!}" label?)
  let singleton ← Expr.reduceStructure args[3]!
  let canonicalSingleton := canonicalArgs[3]!
  let canonicalSingletonArgs := canonicalSingleton.getAppArgs
  let zero ← if singleton.isAppOfArity ``Singleton.singleton 4 then do
      let singletonArgs := singleton.getAppArgs
      unless ← isDefEq singletonArgs[2]! canonicalSingletonArgs[2]! do
        return .error (← rowError body "unsupported singleton instance" label?)
      pure singletonArgs[3]!
    else if singleton.isAppOfArity ``Set.singleton 2 then
      pure singleton.getAppArgs[1]!
    else
      return .error (← rowError body "expected the canonical singleton zero set" label?)
  let zero ← Expr.reduceStructure zero
  let canonicalZero := canonicalSingletonArgs[3]!
  let zeroArgs := zero.getAppArgs
  let validZero ← if zero.isAppOfArity ``OfNat.ofNat 3 then
      pure ((← isDefEq zeroArgs[1]! canonicalZero.getAppArgs[1]!) &&
        (← isDefEq zeroArgs[2]! canonicalZero.getAppArgs[2]!))
    else if zero.isAppOfArity ``Zero.zero 2 then
      isDefEq zeroArgs[1]! explicitZero.getAppArgs[1]!
    else pure false
  unless validZero && (← isDefEq zero canonicalZero) do
    return .error (← rowError body "expected the canonical zero singleton" label?)
  unless ← isDefEq body canonical do
    return .error (← rowError body "membership does not match the canonical zero singleton" label?)
  return .ok value

private def normalizeZeroMembershipRow (predicate domain point body : Expr)
    (provider : Affine.EvidenceProvider) (label? : Option Name) :
    MetaM (Except Expr.Error RowResult) := do
  let data ← singletonZeroData point body label?
  if let .error error := data then return .error error
  let .ok value := data | throwError "internal error: missing checked singleton membership"
  let source ← mkLambdaFVars #[point] value
  let affine ← Affine.reifyAffine source provider
  if let .error error := affine then
    return .error (← rowError error.expression m!"cone coordinates: {error.reason}" label?)
  let .ok affine := affine | throwError "internal error: missing singleton coordinates"
  let (constraint, pointwiseIff) ← Space.withCanonicalSpaces domain (← inferType value) do
    let constraint ← instantiateMVars (← mkAppM ``Morew.Conic.Constraint.eqZero #[affine.map])
    let pointwiseIff ← instantiateMVars (← mkAppM ``normalizeZeroMembership
      #[affine.map, source, affine.pointwiseEquality])
    if constraint.hasMVar || pointwiseIff.hasMVar then
      throwError "row construction left unresolved metavariables"
    let holds ← mkAppM ``Morew.Conic.Constraint.Holds #[constraint, point]
    let expected ← mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
    checkWithKernel constraint
    checkWithKernel pointwiseIff
    unless ← isDefEq (← inferType pointwiseIff) expected do
      throwError "row equivalence did not match the input predicate"
    return (constraint, pointwiseIff)
  return .ok { constraint, pointwiseIff }

private def normalizePositiveSemidefiniteRow (predicate domain point body : Expr)
    (provider : Affine.EvidenceProvider) (label? : Option Name) :
    MetaM (Except Expr.Error RowResult) := do
  let value := body.getAppArgs.back!
  let .forallE _ row columnType _ ← whnf (← inferType value)
    | return .error (← rowError body "PSD coordinates require a square real matrix indexed by Fin n" label?)
  let .forallE _ column scalar _ ← whnf columnType
    | return .error (← rowError body "PSD coordinates require a square real matrix indexed by Fin n" label?)
  let row ← whnf row
  let column ← whnf column
  unless row.isAppOfArity ``Fin 1 && column.isAppOfArity ``Fin 1 &&
      (← isDefEq row column) && (← whnf scalar).isConstOf ``Real do
    return .error (← rowError body "PSD coordinates require a square real matrix indexed by Fin n; use fromBlocksFin for block indexing" label?)
  let n := row.getAppArgs[0]!
  if ← Expr.depends point n then
    return .error (← rowError body "PSD matrix dimension depends on the decision point" label?)
  let canonical := (mkAppN (← getConstInfo ``canonicalPositiveSemidefinite).value!
    #[n, value]).headBeta
  let arguments := body.getAppArgs
  let canonicalArguments := canonical.getAppArgs
  unless arguments.size == canonicalArguments.size do
    return .error (← rowError body "PSD predicate has an unsupported instance signature" label?)
  for index in [:arguments.size - 1] do
    unless ← isDefEq arguments[index]! canonicalArguments[index]! do
      return .error (← rowError body "PSD predicate uses unsupported scalar or matrix instances" label?)
  unless ← isDefEq body canonical do
    return .error (← rowError body "PSD predicate uses unsupported scalar or matrix instances" label?)
  let source ← mkLambdaFVars #[point] value
  let affine ← Affine.reifyAffine source provider
  let .ok affine := affine
    | let .error error := affine
        | throwError "internal error: missing affine PSD coordinates"
      return .error (← rowError error.expression m!"PSD matrix entry or block: {error.reason}" label?)
  let some symmetric ← Symmetry.prove? point value
    | return .error (← rowError value
        m!"missing global matrix symmetry: required ∀ point, ({source} point).IsSymm; supply an all-point symmetry proof or a structurally symmetric expression" label?)
  let cone ← mkAppM ``Morew.Conic.Cone.positiveSemidefinite #[n]
  let target ← mkAppM ``Morew.Conic.SymmetricMatrix #[n]
  let (constraint, membershipIff) ← Space.withCanonicalConeSpaces domain target do
    let certificate ← Affine.Space.withCanonicalSpaces #[domain, ← inferType value, target] do
      let ordinary ← mkAppM ``Morew.Affine.Certified.mk
        #[affine.map, affine.pointwiseEquality]
      instantiateMVars (← mkAppM ``Morew.Affine.Certified.toSymmetricMatrix
        #[ordinary, symmetric])
    let map ← mkProjection certificate `map
    let correct ← mkProjection certificate `correct
    let lifted ← mkLambdaFVars #[point]
      (← mkAppM ``Morew.Conic.SymmetricMatrix.ofMatrix #[value, mkApp symmetric point])
    return (← instantiateMVars (← mkAppM ``Morew.Conic.Constraint.mk #[cone, map]),
      ← instantiateMVars (← mkAppM ``normalizeMembership #[cone, map, lifted, correct]))
  let conversion ← mkAppM ``positiveSemidefiniteMembership #[value, mkApp symmetric point]
  let normalizedBody := (← inferType conversion).getAppArgs[1]!
  let normalized ← mkLambdaFVars #[point] normalizedBody
  let normalizationProof ← mkLambdaFVars #[point] conversion
  let pointwiseIff ← mkLambdaFVars #[point]
    (← mkAppM ``Iff.trans #[mkApp membershipIff point, ← mkAppM ``Iff.symm #[conversion]])
  for proof in #[constraint, pointwiseIff, normalizationProof] do
    if proof.hasMVar || (← Evidence.hasPlaceholders proof) then
      throwError "PSD certification left incomplete proof evidence"
    checkWithKernel proof
  let constraintType ← inferType constraint
  let holds := mkAppN
    (mkConst ``Morew.Conic.Constraint.Holds constraintType.getAppFn.constLevels!)
    (constraintType.getAppArgs ++ #[constraint, point])
  let expected ← mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
  unless ← isDefEq (← inferType pointwiseIff) expected do
    throwError "PSD row equivalence did not match the input predicate"
  return .ok {
    constraint
    pointwiseIff
    normalization? := some {
      predicate := normalized
      pointwiseIff := normalizationProof
      changed := true }
  }

private def normalizeMembershipRow (predicate domain point body : Expr)
    (provider : Affine.EvidenceProvider) (label? : Option Name) :
    MetaM (Except Expr.Error RowResult) := do
  let data ← membershipData point body label?
  if let .error error := data then return .error error
  let .ok (cone, value) := data
    | throwError "internal error: missing checked membership"
  let source ← mkLambdaFVars #[point] value
  let affine ← Affine.reifyAffine source provider
  if let .error error := affine then
    return .error (← rowError error.expression m!"cone coordinates: {error.reason}" label?)
  let .ok affine := affine
    | return .error (← rowError body "failed to recognize cone coordinates" label?)
  let target ← whnf (← mkAppM ``Morew.Conic.Cone.Space #[cone])
  let (constraint, pointwiseIff) ← Space.withCanonicalConeSpaces domain target do
    let constraint ← instantiateMVars (← mkAppM ``Morew.Conic.Constraint.mk #[cone, affine.map])
    let pointwiseIff ← instantiateMVars (← mkAppM ``normalizeMembership
      #[cone, affine.map, source, affine.pointwiseEquality])
    if constraint.hasMVar || pointwiseIff.hasMVar then
      throwError "row construction left unresolved metavariables"
    let holds ← mkAppM ``Morew.Conic.Constraint.Holds #[constraint, point]
    let expected ← mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
    checkWithKernel constraint
    checkWithKernel pointwiseIff
    unless ← isDefEq (← inferType pointwiseIff) expected do
      throwError "row equivalence did not match the input predicate"
    return (constraint, pointwiseIff)
  return .ok { constraint, pointwiseIff }

private structure FamilyMember where
  coordinates : Expr
  /-- A power parameter and its range proof; `none` denotes the exponential cone. -/
  power? : Option (Expr × Expr) := none

-- Keep evidence lets inside the coordinate function where the affine reifier
-- can use them. Cone parameters retain only their own dependencies, so unused
-- coordinate lets cannot capture the decision point in the bundled cone.
-- Quantifiers, conjunctions, and arbitrary predicate helpers are not opened.
private partial def familyMember (point index body : Expr)
    (label? : Option Name) : MetaM (Except Expr.Error FamilyMember) := do
  let body ← Expr.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      match ← familyMember point index (rest.instantiate1 binding) label? with
      | .error error => return .error error
      | .ok member =>
          let power? ← member.power?.mapM fun (exponent, range) => do
            return (← mkLetFVars #[binding] exponent (generalizeNondepLet := false),
              ← mkLetFVars #[binding] range (generalizeNondepLet := false))
          return .ok {
            coordinates := ← mkLetFVars #[binding] member.coordinates
              (usedLetOnly := false) (generalizeNondepLet := false)
            power?
          }
  unless body.isAppOfArity ``Membership.mem 5 do
    return .error (← rowError body
      "expected one exponential membership or power membership under the finite quantifier" label?)
  match ← membershipData point body label? (some index) with
  | .error error => return .error error
  | .ok (cone, coordinates) =>
      if cone.isConstOf ``Morew.Conic.Cone.exponential then return .ok { coordinates }
      if cone.isAppOfArity ``Morew.Conic.Cone.power 2 then
        return .ok { coordinates, power? := some (cone.getAppArgs[0]!, cone.getAppArgs[1]!) }
      return .error (← rowError body
        "finite quantified rows require the native exponential cone or power cone" label?)

private def normalizeFiniteFamilyRow (predicate domain point body : Expr)
    (provider : Affine.EvidenceProvider) (label? : Option Name) :
    MetaM (Except Expr.Error RowResult) := do
  let .forallE name index rest info := body
    | return .error (← rowError body "expected a finite quantified membership" label?)
  let shape ← whnf index
  unless shape.isAppOfArity ``Fin 1 do
    return .error (← rowError body "quantified cone rows require one index of type Fin n" label?)
  let n := shape.getAppArgs[0]!
  if ← Expr.depends point n then
    return .error (← rowError body "cone dimension depends on the decision point" label?)
  let family : Except Expr.Error FamilyMember ← withLocalDecl name info index fun i => do
    match ← familyMember point i (rest.instantiate1 i) label? with
    | .error error => return .error error
    | .ok member =>
        let power? ← member.power?.mapM fun (exponent, range) => do
          return (← mkLambdaFVars #[i] exponent, ← mkLambdaFVars #[i] range)
        return .ok { coordinates := ← mkLambdaFVars #[point, i] member.coordinates, power? }
  if let .error error := family then return .error error
  let .ok family := family
    | throwError "internal error: missing finite family coordinates"
  let source := family.coordinates
  let affine ← Affine.reifyAffine source provider
  if let .error error := affine then
    return .error (← rowError error.expression m!"cone coordinates: {error.reason}" label?)
  let .ok affine := affine
    | throwError "internal error: missing affine finite family"
  if let some (exponent, range) := family.power? then
    if (← Expr.depends point exponent) || (← Expr.depends point range) then
      return .error (← rowError body "power cone parameter depends on the decision point" label?)
  let (cone, theoremName, parameters) ← match family.power? with
    | none => pure (← mkAppM ``Morew.Conic.Cone.exponentialProduct #[n],
        ``normalizeExponentialFamily, #[n])
    | some (exponent, range) => do
        pure (← mkAppM ``Morew.Conic.Cone.powerProduct #[n, exponent, range],
          ``normalizePowerFamily, #[n, exponent, range])
  let target ← whnf (← mkAppM ``Morew.Conic.Cone.Space #[cone])
  let (constraint, pointwiseIff) ← Space.withCanonicalConeSpaces domain target do
    let constraint ← instantiateMVars (← mkAppM ``Morew.Conic.Constraint.mk #[cone, affine.map])
    let pointwiseIff ← instantiateMVars (← mkAppM theoremName
      (parameters ++ #[affine.map, source, affine.pointwiseEquality]))
    if constraint.hasMVar || pointwiseIff.hasMVar then
      throwError "quantified row construction left unresolved metavariables"
    let holds ← mkAppM ``Morew.Conic.Constraint.Holds #[constraint, point]
    let expected ← mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
    checkWithKernel constraint
    checkWithKernel pointwiseIff
    unless ← isDefEq (← inferType pointwiseIff) expected do
      throwError "quantified row equivalence did not match the input predicate"
    return (constraint, pointwiseIff)
  return .ok { constraint, pointwiseIff }

private def normalizeRowWithInstances (predicate : Expr) (provider : Affine.EvidenceProvider)
    (label? : Option Name) : MetaM (Except Expr.Error RowResult) := do
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | return .error (← rowError predicate "expected a predicate on the decision space" label?)
  unless codomain == mkSort Level.zero do
    return .error (← rowError predicate "expected a predicate on the decision space" label?)
  withLocalDeclD `point domain fun point =>
    -- Preserve the typed relation head while eliminating language-level
    -- wrappers, including the product patterns used by the surface DSL.
    withPredicateLets point (mkApp predicate point) fun body => do
      if body.isAppOf ``Matrix.PosSemidef then
        return ← normalizePositiveSemidefiniteRow predicate domain point body provider label?
      if body.isAppOfArity ``Membership.mem 5 then
        if (← whnfUntil body.getAppArgs[1]! ``Set).isSome then
          unless (← Expr.reduceStructure body.getAppArgs[3]!).isAppOfArity
              ``Morew.Conic.Cone.powerSet 1 do
            return ← normalizeZeroMembershipRow predicate domain point body provider label?
        return ← normalizeMembershipRow predicate domain point body provider label?
      if body.isForall then
        return ← normalizeFiniteFamilyRow predicate domain point body provider label?
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
      let left ← Affine.reifyAffine lhs provider
      if let .error error := left then
        return .error (← rowError error.expression m!"left-hand side: {error.reason}" label?)
      let .ok left := left
        | return .error (← rowError body "failed to recognize the left-hand side" label?)
      let right ← Affine.reifyAffine rhs provider
      if let .error error := right then
        return .error (← rowError error.expression m!"right-hand side: {error.reason}" label?)
      let .ok right := right
        | return .error (← rowError body "failed to recognize the right-hand side" label?)
      let (constraint, pointwiseIff) ← Space.withCanonicalSpaces domain target do
        let difference ← if equality || greaterEqual then
            mkAppM ``subtractMaps #[left.map, right.map]
          else
            mkAppM ``subtractMaps #[right.map, left.map]
        let constructor := if equality then
            ``Morew.Conic.Constraint.eqZero
          else ``Morew.Conic.Constraint.nonnegative
        let constraint ← instantiateMVars (← mkAppM constructor #[difference])
        let theoremName := if equality then ``normalizeEq else ``normalizeLE
        let proofArguments := if greaterEqual then
            #[right.map, left.map, rhs, lhs, right.pointwiseEquality, left.pointwiseEquality]
          else
            #[left.map, right.map, lhs, rhs, left.pointwiseEquality, right.pointwiseEquality]
        let pointwiseIff ← instantiateMVars (← mkAppM theoremName proofArguments)
        if constraint.hasMVar || pointwiseIff.hasMVar then
          throwError "row construction left unresolved metavariables"
        let holds ← mkAppM ``Morew.Conic.Constraint.Holds #[constraint, point]
        let expected ← mkForallFVars #[point] (← mkAppM ``Iff #[holds, mkApp predicate point])
        checkWithKernel constraint
        checkWithKernel pointwiseIff
        unless ← isDefEq (← inferType pointwiseIff) expected do
          throwError "row equivalence did not match the input predicate"
        return (constraint, pointwiseIff)
      return .ok { constraint, pointwiseIff }

private def withFiniteInstances (instances : List Expr)
    (action : MetaM (Except Expr.Error RowResult)) :
    MetaM (Except Expr.Error RowResult) := do
  match instances with
  | [] => action
  | inst :: rest =>
    withLetDecl `_sourceFinite (← inferType inst) inst fun binding => do
      match ← withFiniteInstances rest action with
      | .error error => return .error error
      | .ok result => return .ok (← result.mapExprM (·.replaceFVarsM #[binding] #[inst]))

private def normalizeRowCore (predicate : Expr) (provider : Affine.EvidenceProvider)
    (label? : Option Name) : MetaM (Except Expr.Error RowResult) := do
  let predicate ← instantiateMVars predicate
  if ← hasUnresolved predicate then
    return .error (← rowError predicate "unresolved metavariables in predicate" label?)
  withFiniteInstances (← Expr.sourceFiniteInstances predicate).toList do
    normalizeRowWithInstances predicate provider label?

/-- Normalize an elaborated scalar or vector `=`, `≤`, or `≥` row, a canonical
zero singleton, native nonnegative, zero, second-order, exponential, power or PSD cone
membership, ordinary matrix PSD, or one finite quantified family of exponential or power memberships.
Every cone coordinate must be affine.
The optional label supplies diagnostic context without depending on source
syntax or presentation metadata. -/
def normalizeRow (predicate : Expr) (provider : Affine.EvidenceProvider := {})
    (label? : Option Name := none) : MetaM (Except Expr.Error RowResult) :=
  State.withIsolatedMVars do
    try
      let direct ← State.withIsolatedMVars do
        try
          normalizeRowCore predicate provider label?
        catch error =>
          return .error (← rowError predicate error.toMessageData label?)
      if let .ok result := direct then return .ok result
      if ← hasUnresolved predicate then return direct
      let instances ← Affine.helperFiniteInstances predicate
      if instances.isEmpty then return direct
      withFiniteInstances instances.toList do
        normalizeRowCore predicate provider label?
    catch error =>
      return .error (← rowError predicate error.toMessageData label?)

/-- Recognize the real objective retained by a typed presentation. The explicit
optimization sense and order-dual annotation remain in the presentation. -/
def reifyObjective (presentation : Reformulation.PresentationState)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error Affine.AffineResult) :=
  State.withIsolatedMVars do
    let fail (expression : Expr) (reason : MessageData) :
        MetaM (Except Expr.Error Affine.AffineResult) := do
      return .error {
        expression
        reason := ← addMessageContext m!"objective: {reason}"
      }
    try
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
      match ← Affine.reifyAffine presentation.objective provider with
      | .ok result => return .ok result
      | .error error => fail error.expression error.reason
    catch error =>
      fail presentation.objective error.toMessageData

/-- Normalize a typed named constraint, retaining its label in diagnostics. -/
def normalizeConstraint (entry : Reformulation.ConstraintEntry)
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Expr.Error RowResult) :=
  normalizeRow entry.predicate provider (some entry.name)

end Morew.Elab.Conic
