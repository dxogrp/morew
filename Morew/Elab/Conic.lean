/-
Copyright 2026 Hao Zhu
SPDX-License-Identifier: Apache-2.0
-/

import Morew.Conic
import Morew.Elab.Affine
import Morew.Elab.Affine.State
import Morew.Elab.Conic.Space
import Morew.Elab.Reformulation.Presentation

/-!
# Checked affine row normalization

This internal API recognizes elaborated scalar and finite-vector equality and
inequality predicates, and native second-order and exponential cone membership.
A finite family of exponential memberships remains one quantified presentation
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

private theorem normalizeMembership
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (cone : Morew.Conic.Cone) (map : X →ᵃ[ℝ] cone.Space)
    (source : X → cone.Space) (h : ∀ x, map x = source x) :
    ∀ x, (Morew.Conic.Constraint.mk cone map).Holds x ↔ source x ∈ cone.carrier := by
  intro x
  change map x ∈ cone.carrier ↔ source x ∈ cone.carrier
  rw [h x]

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

-- Keep decision-independent lets available, including denominator proofs and
-- instances. Dependent lets must be substituted before abstracting the point;
-- independent values are substituted into both results before leaving scope.
private partial def withPredicateLets (point body : Expr)
    (action : Expr → MetaM (Except Affine.AffineError RowResult)) :
    MetaM (Except Affine.AffineError RowResult) := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    if (← Affine.depends point type) || (← Affine.depends point value) then
      return ← withPredicateLets point (rest.instantiate1 value) action
    withLetDecl name type value (nondep := nondep) fun binding => do
      match ← withPredicateLets point (rest.instantiate1 binding) action with
      | .error error => return .error error
      | .ok result =>
        return .ok {
          constraint := ← result.constraint.replaceFVarsM #[binding] #[value]
          pointwiseIff := ← result.pointwiseIff.replaceFVarsM #[binding] #[value]
        }
  else
    action body

private def membershipData (point body : Expr) (label? : Option Name) :
    MetaM (Except Affine.AffineError (Expr × Expr)) := do
  let args := body.getAppArgs
  let carrier ← Affine.reduceStructure args[3]!
  let carrier := if carrier.isConstOf ``Morew.Conic.Cone.nonnegativeScalarCarrier then
      mkApp (mkConst ``Morew.Conic.Cone.carrier)
        (mkConst ``Morew.Conic.Cone.nonnegativeScalar)
    else carrier
  unless carrier.isAppOfArity ``Morew.Conic.Cone.carrier 1 do
    return .error (← rowError body "expected native supported cone membership" label?)
  let cone ← Affine.reduceStructure carrier.getAppArgs[0]!
  unless cone.isAppOfArity ``Morew.Conic.Cone.secondOrder 1 ||
      cone.isAppOfArity ``Morew.Conic.Cone.rotatedSecondOrder 1 ||
      cone.isAppOfArity ``Morew.Conic.Cone.zero 1 ||
      cone.isAppOfArity ``Morew.Conic.Cone.nonnegative 1 ||
      cone.isConstOf ``Morew.Conic.Cone.nonnegativeScalar ||
      cone.isConstOf ``Morew.Conic.Cone.exponential ||
      cone.isAppOfArity ``Morew.Conic.Cone.exponentialProduct 1 do
    return .error (← rowError body m!"unsupported cone {cone}" label?)
  if ← Affine.depends point cone then
    return .error (← rowError body "cone dimension depends on the decision point" label?)
  let value := args[4]!
  let template := (← getConstInfo ``canonicalMembership).value!
  let canonical := (mkAppN template #[cone, value]).headBeta
  let canonicalArgs := canonical.getAppArgs
  unless ← isDefEq args[2]! canonicalArgs[2]! do
    return .error (← rowError body m!"unsupported membership instance {args[2]!}" label?)
  unless ← isDefEq body canonical do
    return .error (← rowError body "membership does not match the canonical cone" label?)
  return .ok (cone, value)

/-- Recover a native scalar nonnegative-cone coordinate after checking its
membership instance. This does not unfold wrappers or certify affinity. -/
def nonnegativeScalarValue? (point body : Expr) : MetaM (Option Expr) := do
  let result : Except Unit Expr ← Affine.withIsolatedMVars do
    if !(body.isAppOfArity ``Membership.mem 5) || (← hasUnresolved body) then
      return .error ()
    match ← membershipData point body none with
    | .ok (cone, value) =>
        return if cone.isConstOf ``Morew.Conic.Cone.nonnegativeScalar then .ok value else .error ()
    | .error _ => return .error ()
  return result.toOption

private def singletonZeroData (point body : Expr) (label? : Option Name) :
    MetaM (Except Affine.AffineError Expr) := do
  let args := body.getAppArgs
  let value := args[4]!
  let target ← whnf args[0]!
  let (canonical, explicitZero) ← if target.isConstOf ``Real then do
      pure ((mkApp (← getConstInfo ``canonicalScalarZeroMembership).value! value).headBeta,
        (← getConstInfo ``canonicalScalarZero).value!)
    else do
      let .forallE _ index range _ := target
        | return .error (← rowError body "expected a real scalar or finite-vector zero singleton" label?)
      unless !range.hasLooseBVars && (← whnf range).isConstOf ``Real do
        return .error (← rowError body "expected a real scalar or finite-vector zero singleton" label?)
      let index ← whnf index
      unless index.isAppOfArity ``Fin 1 do
        return .error (← rowError body "expected a finite-vector zero singleton" label?)
      let dimension := index.getAppArgs[0]!
      if ← Affine.depends point dimension then
        return .error (← rowError body "cone dimension depends on the decision point" label?)
      pure ((mkAppN (← getConstInfo ``canonicalVectorZeroMembership).value!
        #[dimension, value]).headBeta,
        (mkApp (← getConstInfo ``canonicalVectorZero).value! dimension).headBeta)
  let canonicalArgs := canonical.getAppArgs
  unless ← isDefEq args[2]! canonicalArgs[2]! do
    return .error (← rowError body m!"unsupported membership instance {args[2]!}" label?)
  let singleton ← Affine.reduceStructure args[3]!
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
  let zero ← Affine.reduceStructure zero
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
    MetaM (Except Affine.AffineError RowResult) := do
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

private def normalizeMembershipRow (predicate domain point body : Expr)
    (provider : Affine.EvidenceProvider) (label? : Option Name) :
    MetaM (Except Affine.AffineError RowResult) := do
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

-- Keep evidence lets inside the coordinate function where the affine reifier
-- can use them. Quantifiers, conjunctions, and arbitrary helpers are not opened.
private partial def exponentialFamilyCoordinates (point body : Expr)
    (label? : Option Name) : MetaM (Except Affine.AffineError Expr) := do
  let body ← Affine.reduceStructure body (preserveLets := true)
  if let .letE name type value rest nondep := body then
    return ← withLetDecl name type value (nondep := nondep) fun binding => do
      match ← exponentialFamilyCoordinates point (rest.instantiate1 binding) label? with
      | .error error => return .error error
      | .ok coordinates =>
          return .ok (← mkLetFVars #[binding] coordinates
            (usedLetOnly := false) (generalizeNondepLet := false))
  unless body.isAppOfArity ``Membership.mem 5 do
    return .error (← rowError body
      "expected one exponential membership under the finite quantifier" label?)
  match ← membershipData point body label? with
  | .error error => return .error error
  | .ok (cone, coordinates) =>
      unless cone.isConstOf ``Morew.Conic.Cone.exponential do
        return .error (← rowError body
          "finite quantified rows require the native exponential cone" label?)
      return .ok coordinates

private def normalizeExponentialFamilyRow (predicate domain point body : Expr)
    (provider : Affine.EvidenceProvider) (label? : Option Name) :
    MetaM (Except Affine.AffineError RowResult) := do
  let .forallE name index rest info := body
    | return .error (← rowError body "expected a finite quantified membership" label?)
  let shape ← whnf index
  unless shape.isAppOfArity ``Fin 1 do
    return .error (← rowError body "quantified cone rows require one index of type Fin n" label?)
  let n := shape.getAppArgs[0]!
  if ← Affine.depends point n then
    return .error (← rowError body "cone dimension depends on the decision point" label?)
  let coordinates : Except Affine.AffineError Expr ← withLocalDecl name info index fun i => do
    match ← exponentialFamilyCoordinates point (rest.instantiate1 i) label? with
    | .error error => return .error error
    | .ok value => return .ok (← mkLambdaFVars #[point, i] value)
  if let .error error := coordinates then return .error error
  let .ok source := coordinates
    | throwError "internal error: missing exponential family coordinates"
  let affine ← Affine.reifyAffine source provider
  if let .error error := affine then
    return .error (← rowError error.expression m!"cone coordinates: {error.reason}" label?)
  let .ok affine := affine
    | throwError "internal error: missing affine exponential family"
  let cone ← mkAppM ``Morew.Conic.Cone.exponentialProduct #[n]
  let target ← whnf (← mkAppM ``Morew.Conic.Cone.Space #[cone])
  let (constraint, pointwiseIff) ← Space.withCanonicalConeSpaces domain target do
    let constraint ← instantiateMVars (← mkAppM ``Morew.Conic.Constraint.mk #[cone, affine.map])
    let pointwiseIff ← instantiateMVars (← mkAppM ``normalizeExponentialFamily
      #[n, affine.map, source, affine.pointwiseEquality])
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
    (label? : Option Name) : MetaM (Except Affine.AffineError RowResult) := do
  let type ← whnf (← inferType predicate)
  let .forallE _ domain codomain _ := type
    | return .error (← rowError predicate "expected a predicate on the decision space" label?)
  unless codomain == mkSort Level.zero do
    return .error (← rowError predicate "expected a predicate on the decision space" label?)
  withLocalDeclD `point domain fun point =>
    -- Preserve the typed relation head while eliminating language-level
    -- wrappers, including the product patterns used by the surface DSL.
    withPredicateLets point (mkApp predicate point) fun body => do
      if body.isAppOfArity ``Membership.mem 5 then
        if (← Affine.reduceStructure body.getAppArgs[1]!).isAppOfArity ``Set 1 then
          return ← normalizeZeroMembershipRow predicate domain point body provider label?
        return ← normalizeMembershipRow predicate domain point body provider label?
      if body.isForall then
        return ← normalizeExponentialFamilyRow predicate domain point body provider label?
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
    (action : MetaM (Except Affine.AffineError RowResult)) :
    MetaM (Except Affine.AffineError RowResult) := do
  match instances with
  | [] => action
  | inst :: rest =>
    withLetDecl `_sourceFinite (← inferType inst) inst fun binding => do
      match ← withFiniteInstances rest action with
      | .error error => return .error error
      | .ok result => return .ok {
          constraint := ← result.constraint.replaceFVarsM #[binding] #[inst]
          pointwiseIff := ← result.pointwiseIff.replaceFVarsM #[binding] #[inst]
        }

private def normalizeRowCore (predicate : Expr) (provider : Affine.EvidenceProvider)
    (label? : Option Name) : MetaM (Except Affine.AffineError RowResult) := do
  let predicate ← instantiateMVars predicate
  if ← hasUnresolved predicate then
    return .error (← rowError predicate "unresolved metavariables in predicate" label?)
  withFiniteInstances (← Affine.sourceFiniteInstances predicate).toList do
    normalizeRowWithInstances predicate provider label?

/-- Normalize an elaborated scalar or vector `=`, `≤`, or `≥` row, a canonical
zero singleton, native nonnegative, zero, second-order, or exponential cone
membership, or one finite quantified family of exponential memberships.
Every cone coordinate must be affine.
The optional label supplies diagnostic context without depending on source
syntax or presentation metadata. -/
def normalizeRow (predicate : Expr) (provider : Affine.EvidenceProvider := {})
    (label? : Option Name := none) : MetaM (Except Affine.AffineError RowResult) :=
  Affine.withIsolatedMVars do
    try
      let direct ← Affine.withIsolatedMVars do
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
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError Affine.AffineResult) :=
  Affine.withIsolatedMVars do
    let fail (expression : Expr) (reason : MessageData) :
        MetaM (Except Affine.AffineError Affine.AffineResult) := do
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
    (provider : Affine.EvidenceProvider := {}) : MetaM (Except Affine.AffineError RowResult) :=
  normalizeRow entry.predicate provider (some entry.name)

end Morew.Elab.Conic
